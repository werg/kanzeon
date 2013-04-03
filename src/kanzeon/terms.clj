(ns kanzeon.terms
   (:require [clojure.set :as cset]))

(defprotocol Subsumer
  "Basic behavior or something that when given a term can provide substitutions leading to that term."
  (subsume [this term] [this term path-prefix] [this term path-prefix open?]
    "Return a map of paths to substituted terms, if a path-prefix is provided all paths are appended to it."))

(defn subsume* [prototype term path-prefix open?]
  "Generic subsume operation returns a map of paths-to-values (so under this path we substitute that).

   If possible relies on polymorphic dispatch of the Subsumer protocol."
  (if (= prototype term)
    {} ; since they are the same, there is nothing to substitute
    (if (satisfies? Subsumer prototype)
      (subsume prototype term path-prefix open?)
      (if (and open? (satisfies? Subsumer term) (subsume term prototype [] open?))
        {}
        nil))))

(extend-type clojure.lang.Symbol
;; Here we implement subsumption for symbols.
;; It is assumed that a symbol will subsume any term, simply by sybstituting to that term.
  Subsumer
  (subsume
    ([this term]
       (subsume this term [] false))
    ([this term path-prefix]
       (subsume this term path-prefix false))
    ([this term path-prefix open?]
       (if (nil? term)
         (if open?
           {}
           nil)
         {path-prefix term}))))

;; how about an open version?
;; it should work for symbols
;; and below we only need to add another term to the subset? test

(defn subsume-keys [prototype term parent-keys child-keys path-prefix open?]
  "For a structural element with keys (so either map or sequence), compute substitutions recursively."
  (let [pk (set parent-keys)
        ck (set child-keys)]
    (when (or (= pk ck) (cset/subset? pk ck) open?)
      (let [ext-keys (cset/difference ck pk)
            exts (zipmap (map conj (repeat path-prefix) ext-keys)
                         (map get (repeat term) ext-keys))
            substs (loop [substs {} pk pk]
                     (if (empty? pk)
                       substs
                       (let [p (first pk)]
                         (if-let [subst (subsume*
                                         (get prototype p)
                                         (get term p)
                                         (conj path-prefix p)
                                         open?)]
                           (recur (merge substs subst) (rest pk))
                           nil))))]
        (if (nil? substs)
          nil
          (merge exts substs))))))

(defprotocol Keyable
  (subs-keys [this]
    "Returns keys of substructures."))

(extend-type nil
  Subsumer
  (subsume
    ([this term] (prn nil :subsume term))
    ([this term path-prefix]
       (prn nil :subsume term path-prefix))
    ([this term path-prefix open?]
       (prn nil :subsume term path-prefix open?)
       (when open?
         {path-prefix term}))))

(extend-type clojure.lang.Sequential
  Keyable
  (subs-keys [this]
    (range (count this))))

(extend-type clojure.lang.IPersistentMap
  Keyable
  (subs-keys [this]
    (keys this)))

(extend-type clojure.lang.IPersistentMap
  Subsumer 
 (subsume
    ([this term]
       (subsume this term [] false))
   ([this term path-prefix]
      (subsume this term path-prefix false))
   ([this term path-prefix open?]
      (if (satisfies? Keyable term)
        (let [parent-keys (keys this)
              child-keys (subs-keys term)]
          (subsume-keys this term parent-keys child-keys path-prefix open?))
        (when (and open? (satisfies? Subsumer term) (subsume term this [] open?))
          {})))))


(defprotocol AntiUnifiable
  (anti-unify [this term] [this term path-prefix]))

(extend-type clojure.lang.Symbol
  AntiUnifiable
  (anti-unify
    ([this term path-prefix]
    {:lgg this ; should this return '_ ?
     :diff1 {}
     :diff2 (if (instance? clojure.lang.Symbol term)
              {}
              {path-prefix term})})
    ([this term]
       (anti-unify this term []))))

;; todo: this does not work for lists!!!

(defn- get-diff [hm keys path-prefix]
  (into {} (map #(vector (conj path-prefix %) (hm %)) keys)))

(defn anti-unify-keyables
  ([this term]
     (anti-unify this term []))
  ([this term path-prefix]
     (if (satisfies? Keyable term)
       (let [keys1 (set (subs-keys this))
             keys2  (set (subs-keys term))]
         (loop [ldiff1 (get-diff this (cset/difference keys1 keys2) path-prefix)
                ldiff2 (get-diff term (cset/difference keys2 keys1) path-prefix)
                inter-keys (cset/intersection keys1 keys2)
                llgg (empty this)]
           (if (empty? inter-keys)
             {:lgg llgg
              :diff1 ldiff1
              :diff2 ldiff2}
             (let [ike (first inter-keys)
                   {:keys [lgg diff1 diff2]} (anti-unify (get this ike)
                                                         (get term ike)
                                                         (conj path-prefix ike))]
               (recur (merge ldiff1 diff1)
                      (merge ldiff2 diff2)
                      (rest inter-keys)
                      (assoc llgg ike lgg))))))
       {:lgg '_
        :diff1 {path-prefix this}
        :diff2 {path-prefix term}})))

(extend clojure.lang.IPersistentMap
  AntiUnifiable
  {:anti-unify anti-unify-keyables})

(extend clojure.lang.Sequential
  AntiUnifiable
  {:anti-unify anti-unify-keyables})

(extend-type Object
  AntiUnifiable
  (anti-unify
    ([this term path-prefix]
       (if (= this term)
         {:lgg this
          :diff1 {}
          :diff2 {}}
         (if (instance? clojure.lang.Symbol term)
           {:lgg term
            :diff1 {path-prefix this}
            :diff2 {}}
           {:lgg '_
            :diff1 {path-prefix this}
            :diff2 {path-prefix term}})))
    ([this term]
       (anti-unify this term []))))

(defn compare-substs [subst1 subst2]
  (let [keys1 (set (keys subst1))
        keys2  (set (keys subst2))]
    (loop [ldiff1 (select-keys subst1 (cset/difference keys1 keys2))
           ldiff2 (select-keys subst2 (cset/difference keys2 keys1))
           inter-keys (cset/intersection keys1 keys2)
           linter {}]
      (if (empty? inter-keys)
        {:inter linter
         :diff1 ldiff1
         :diff2 ldiff2}
        (let [ike (first inter-keys)
              {:keys [lgg diff1 diff2]} (anti-unify (get subst1 ike) (get subst2 ike))]
          (recur (merge ldiff1 diff1)
                 (merge ldiff2 diff2)
                 (rest inter-keys)
                 (conj linter [ike lgg])))))))

(defn apply-subst [term subst]
  (loop [term term
         subst (seq subst)]
    (if (empty? subst)
      term
      (let [[path value] (first subst)]
        (if (and (empty? path) (symbol? term) (empty? (rest subst)))
          value
          (recur (assoc-in term path value) (rest subst)))))))

(declare unify-with-nil)

(defn apply-subst-open [term subst]
  (loop [term term
         subst (seq subst)]
    (if (empty? subst)
      term
      (let [[path value] (first subst)]
        (if (and (empty? path) (symbol? term) (empty? (rest subst)))
          value
          (recur (update-in term path unify-with-nil value) (rest subst)))))))

(defn subst-unify [term1 term2 prefix1 prefix2]
  [(subsume term2 term1 prefix1 true)
   (subsume term1 term2 prefix2 true)])

(defn unify
  ([term1 term2]
     (let [[subst1 subst2] (subst-unify term1 term2 [] [])]
       (if (or (nil? subst1) (nil? subst2))
         nil
         (apply-subst term1 subst2)))))

(defn unify-with-nil [term1 term2]
  (if (nil? term1)
    term2
    (if (nil? term2)
      term1
      (unify term1 term2))))

(defn merge-substs [subst1 subst2]
  ;; this does not take into account conflicting substitutions
  (merge-with unify subst1 subst2))

;; shit, how do we deal with the exceptional situation
;; when they conflict? (i.e. don't unify)



;; the set message
;; all items below superterm(s)
;; are also below these terms

;; if all items below these superterms are nil then this is failure?
;; or maybe rather just have a failure event!!!!


;; final discovery of a member (so there are no substructures below, but this is a part)

;; final success vs. final failure
;; tentative


;; get-aggregate
;; update-aggregate?

;; and we can have basic lexical scope
;; so where the resolve function goes up from the local items map to the top level?
;; really? i'm maybe not that sure -- whether lower level clauses should be able to constrain higher levels... that's advanced


