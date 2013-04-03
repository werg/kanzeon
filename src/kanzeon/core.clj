(ns kanzeon.core
  (:require [kanzeon.terms]))

{:items {}
 :agenda []
 :meta {}}

(def unify kanzeon.terms/unify-with-nil)

;;todo: move up to persisters nil and :add-unify



;; persisters are able to fail and to emit custom notes
;; :abort? (failing) will halt the propagation of the notification

(def call-fns 
  {:term {:get-val (fn [item args]
                       (:val item))}
   })

(defn call [function path args items]
  (let [item (get-in items path)]
    ((get-in call-fns [(:kind item) function]) item args)))

(def persisters
  {:term {:substitute (fn [our-path {:keys [subst-path val] :as note} items]
                        (let [subst-path (cons subst-path :val)
                              item (get-in items our-path)
                              nested (get-in item subst-path)
                              resolver (if-let [resolver (:resolver note)] 
                                         resolver
                                         unify)]
                          (if-let [resolved (resolver val nested)]
                            {:item (assoc-in item subst-path resolved)
                             :abort? false}
                            {:item item
                             :abort? true
                             :notifications (:failure-notes note)})))
          :add-listener (fn [our-path
                             {:keys [args target-path receive note-kind]}
                             items]
                          (let [{:keys [listeners] :as item} (get-in items our-path)]
                            {:items (update-in items (concat our-path
                                                             [:listeners note-kind])
                                              concat {:target-path target-path
                                                      :receive receive
                                                      :args args})}))}
   :== {:init (fn [our-path note items]
                (let [item (get-in items our-path)
                      unifiers (:unifiers item)]
                  {:items items
                   :notifications (map #(hash-map :kind :init-unifier
                                                  :path our-path
                                                  :unifier (second %)
                                                  :source-key (first %))
                                       unifiers)}))
        :init-unifier (fn [our-path {:keys [unifier source-key]} items]
                        (let [{:keys [item-path]} unifier]
                          {:items items
                             :notifications [{:kind :add-listener
                                              :note-kind :substitute
                                              :receive :prop-subst
                                              :path item-path
                                              :args {:source-key source-key}
                                              :target-path our-path}]}))}})

;; a fail event might be emitted automatically too
;; listeners can attach to the event itself



(defn persist [note items]
  (let [{:keys [path kind]} note
        item (get-in items path)
        item-kind (:kind item)
        persister (get-in persisters [item-kind kind])]
    (if persister ; we could add a :must-persist flag if we want to raise an exception
      (let [{:keys [items abort? notifications]} (persister path note items)]
        {:items items
         :persist-notes notifications
         :abort? abort?})
      {:items items
       :exceptions []})))

{:kind :==
 :unifiers {}}

;; subst-path
;; val

;(if source-subst-path.. )
;; handle the whole source, note subst path thing

(def receivers
  {:== {:prop-subst (fn [our-path note args items]
                      ;; create substitutions
                      (let [item (get-in items our-path)
                            unifiers (:unifiers item)
                            source-key (:source-key args)
                            
                            source-subst-path (get-in unifiers [source-key :subst-path])
                            unifiers (dissoc unifiers source-key)
                            {:keys [val propagator]} note]
                        (when (not (= propagator our-path))
                          (map #(hash-map :kind :substitute
                                          :resolver unify
                                          :path (:item-path %)
                                          :subst-path (:subst-path %)
                                          :val val
                                          :propagator our-path)
                               (vals unifiers)))))
}})

;; upon initialization we still have to register this as a listener with :prop-subst
;; as the receiver keyword and put the source-key in the args

;; signature: recipient-path, note, args, items

{:listeners {:note-kind [{:target-path nil
                          :receive nil}]}}

(defn dispatch [note items]
  (let [{:keys [path kind]} note
        emitter (get-in items path)
        listeners (get (:listeners emitter) kind)
        target-paths (map :target-path listeners)
        targets (map get-in (repeat items) target-paths)
        target-kinds (map :kind targets)

        rec-kwds (map :receive listeners)
        rec-funs (map get (map receivers target-kinds) rec-kwds)

        target-args (map :target-args listeners)]
    (mapcat apply rec-funs
            target-paths (repeat note) target-args (repeat items) (repeat []))))


(defn update [{:keys [agenda items]}]
  (let [note (first agenda)
        {:keys [items persist-notes abort?]} (persist note items)]
    {:items items
     :agenda (sort-by #(not (= (:kind %1))) 
                      (concat (rest agenda)
                              persist-notes
                              (when (not abort?)
                                (dispatch note items))))}))


;; todo:

;; for now we return whole blocks of solutions

;; kinds of items:
;; or
;; clause
;; unify
;; term


;; todo later:
;; dispatch (more elaborate)