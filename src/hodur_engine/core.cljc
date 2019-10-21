(ns hodur-engine.core
  (:require #?@(:clj
                [[clojure.edn :as edn]
                 [clojure.java.io :as io]])
            [camel-snake-kebab.core :refer [->camelCaseKeyword
                                            ->PascalCaseKeyword
                                            ->kebab-case-keyword
                                            ->snake_case_keyword]]
            [clojure.string :as string]
            [datascript.core :as d]
            [datascript.query-v3 :as q])
  #?(:clj
     (:import (java.util.jar JarFile JarEntry))))

(def ^:private temp-id-counter (atom 0))

(def ^:private temp-id-map (atom {}))

(def ^:private meta-schema
  {;;general meta nodes
   :node/type             {:db/index true}

   ;;type meta nodes
   :type/name             {:db/unique :db.unique/identity}
   :type/qualified-name   {:db/unique :db.unique/identity}
   :type/kebab-case-name  {:db/unique :db.unique/identity}
   :type/PascalCaseName   {:db/unique :db.unique/identity}
   :type/camelCaseName    {:db/unique :db.unique/identity}
   :type/snake_case_name  {:db/unique :db.unique/identity}
   :type/implements       {:db/cardinality :db.cardinality/many
                           :db/valueType   :db.type/ref}
   :type/interface        {:db/index true}
   :type/enum             {:db/index true}
   :type/union            {:db/index true}

   ;;field meta nodes
   :field/name            {:db/index true}
   :field/qualified-name  {:db/index true}
   :field/kebab-case-name {:db/index true}
   :field/PascalCaseName  {:db/index true}
   :field/camelCaseName   {:db/index true}
   :field/snake_case_name {:db/index true}
   :field/parent          {:db/cardinality :db.cardinality/one
                           :db/valueType   :db.type/ref}
   :field/type            {:db/cardinality :db.cardinality/one
                           :db/valueType   :db.type/ref}
   :field/union-type      {:db/cardinality :db.cardinality/one
                           :db/valueType   :db.type/ref}

   ;;param meta nodes
   :param/name            {:db/index true}
   :param/qualified-name  {:db/index true}
   :param/kebab-case-name {:db/index true}
   :param/PascalCaseName  {:db/index true}
   :param/camelCaseName   {:db/index true}
   :param/snake_case_name {:db/index true}
   :param/parent          {:db/cardinality :db.cardinality/one
                           :db/valueType   :db.type/ref}
   :param/type            {:db/cardinality :db.cardinality/one
                           :db/valueType   :db.type/ref}})

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FIXME: move these to a README/TUTORIAL when one is available
;; Some queries
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def all-interfaces
  '[:find [(pull ?t [* {:type/_implements [*]}]) ...]
    :where
    [?t :type/interface true]])

(def all-types
  '[:find [(pull ?t [* {:type/implements [*]
                        :field/_parent
                        [* {:field/type [*]
                            :param/_parent
                            [* {:param/type [*]}]}]}]) ...]
    :where
    [?t :type/name]])

(def one-type
  '[:find [(pull ?t [* {:type/implements [*]
                        :field/_parent
                        [* {:field/type [*]
                            :param/_parent
                            [* {:param/type [*]}]}]}]) ...]
    :in $ ?n
    :where
    [?t :type/name ?n]])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Internal utils
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#?(:clj
   (defn ^:private jar-name
     [url]
     (->> url
          .getPath
          (re-matches #"^file:(.*)!.*$")
          last)))

#?(:clj
   (defn ^:private jar-path
     [url]
     (->> url
          .getPath
          (re-matches #"^file:.*!/(.*)$")
          last)))

#?(:clj
   (defn ^:private slurpable-streams [path]
     (let [is-edn? #(string/ends-with? % ".edn")]
       (if (and (= java.net.URL (type path))
                (= "jar" (.getProtocol path)))
         (let [jar (JarFile. (jar-name path))
               jar-path' (jar-path path)]
           (reduce (fn [c ^JarEntry entry]
                     (cond-> c
                       (and (string/starts-with? (.getName entry) jar-path')
                            (is-edn? (.getName entry)))
                       (conj (.getInputStream jar entry))))
                   '() (enumeration-seq (.entries jar))))
         (->> path
              io/file
              file-seq
              (filter #(is-edn? (.getPath ^java.io.File %))))))))

#?(:clj
   (defn ^:private schema-streams
     [paths]
     (mapv slurpable-streams paths)))

#?(:clj
   (defn ^:private slurp-files
     [files]
     (map #(-> % slurp edn/read-string)
          files)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Temp ID state stuff
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn ^:private reset-temp-id-state!
  []
  (reset! temp-id-counter 0)
  (reset! temp-id-map {}))

(defn ^:private next-temp-id!
  []
  (swap! temp-id-counter dec))

(defn ^:private set-temp-id!
  [i]
  (swap! temp-id-map assoc i (next-temp-id!)))

(defn ^:private get-temp-id!
  ([t i r]
   (get-temp-id! (str t "-" i "-" r)))
  ([i]
   (if-let [out (get @temp-id-map i)]
     out
     (get (set-temp-id! i) i))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parsing functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn ^:private implements-reader
  [k & coll]
  {:new-v (map (fn [sym] {:db/id (get-temp-id! sym)})
               (flatten coll))})

(defn ^:private create-type-reader
  [ns]
  (fn [k sym]
    {:new-k (keyword ns "type")
     :new-v {:db/id (get-temp-id! sym)}}))

(defn ^:private expanded-key
  [ns k]
  (if (namespace k)
    k
    (keyword ns (name k))))

(defn ^:private cardinality-reader
  [k v]
  (if (not (vector? v))
    {:new-v [v v]}
    {:new-v v}))

(defn ^:private find-and-run-reader
  [reader-map ns k v]
  (let [expanded-k (expanded-key ns k)
        out {:new-k expanded-k
             :new-v v}]
    (if-let [reader-fn (get reader-map k)]
      (merge out (reader-fn expanded-k v))
      out)))

(defn ^:private apply-metas
  ([ns t default init-map]
   (apply-metas ns t init-map nil))
  ([ns t default init-map reader-map]
   (let [meta-data (merge default (meta t))]
     (reduce-kv (fn [a k v]
                  (let [{:keys [new-k new-v]}
                        (find-and-run-reader reader-map ns k v)]
                    (assoc a new-k new-v)))
                init-map
                meta-data))))

(defn ^:private get-recursive
  [e]
  (let [m (meta e)]
    (reduce-kv
     (fn [a k v]
       (if (= "tag-recursive" (name k))
         (assoc a k v)
         a))
     {} m)))

(defn ^:private merge-recursive
  [base rec sym]
  (reduce-kv
   (fn [m k {:keys [only except] :as v}]
     (let [tag-k (keyword (namespace k) "tag")]
       (cond-> m
         (or only except)
         (dissoc tag-k)

         v
         (assoc tag-k v)

         (and only (some #(= sym %) only))
         (assoc tag-k v)

         (and except (not (some #(= sym %) except)))
         (assoc tag-k v))))
   (or base {}) rec))

(defn ^:private conj-type
  [a t default recursive]
  (conj a (apply-metas
           "type" t (merge-recursive default recursive t)
           {:db/id (get-temp-id! t)
            :node/type :type
            :type/name (str t)
            :type/kebab-case-name (->kebab-case-keyword t)
            :type/camelCaseName (->camelCaseKeyword t)
            :type/PascalCaseName (->PascalCaseKeyword t)
            :type/snake_case_name (->snake_case_keyword t)
            :type/nature :user}
           {:implements implements-reader})))

(defn ^:private conj-params
  [a t field r params default recursive]
  (reduce (fn [accum param]
            (conj accum (apply-metas
                         "param" param (merge-recursive default recursive param)
                         {:node/type :param
                          :param/name (str param)
                          :param/cardinality [1 1]
                          :param/kebab-case-name (->kebab-case-keyword param)
                          :param/PascalCaseName (->PascalCaseKeyword param)
                          :param/camelCaseName (->camelCaseKeyword param)
                          :param/snake_case_name (->snake_case_keyword param)
                          :param/parent {:db/id (get-temp-id! t field r)}}
                         {:type (create-type-reader "param")
                          :tag (create-type-reader "param")
                          :cardinality cardinality-reader})))
          a params))

(defn ^:private conj-fields
  [a t fields default recursive]
  (loop [accum a
         field (first fields)
         last-field nil
         last-r nil
         next-fields (next fields)]
    (if (nil? field)
      accum
      (let [r (rand)
            new-accum
            (cond
              ;; is a field proper
              (symbol? field)
              (let [recursive (merge recursive (get-recursive field))
                    merged-default (merge-recursive default recursive field)
                    union-field? (-> t meta :union)
                    init-map (cond-> {:db/id (get-temp-id! t field r)
                                      :node/type :field
                                      :field/name (str field)
                                      :field/cardinality [1 1]
                                      :field/kebab-case-name (->kebab-case-keyword field)
                                      :field/PascalCaseName (->PascalCaseKeyword field)
                                      :field/camelCaseName (->camelCaseKeyword field)
                                      :field/snake_case_name (->snake_case_keyword field)
                                      :field/parent {:db/id (get-temp-id! t)}}
                               union-field? (assoc :field/union-type (get-temp-id! field)))]
                (conj accum (apply-metas
                             "field" field
                             merged-default
                             init-map
                             {:type (create-type-reader "field")
                              :tag (create-type-reader "field")
                              :cardinality cardinality-reader})))

              ;; is a coll of params
              (seqable? field)
              (let [recursive (merge recursive (get-recursive last-field))]
                (conj-params accum t last-field last-r field
                             default recursive))

              :default
              accum)]
        (recur new-accum
               (first next-fields)
               field
               r
               (next next-fields))))))

(defn ^:private parse-types
  [accum types]
  (let [has-default? (= (first types) 'default)
        real-types (if has-default? (next types) types)
        default (if has-default? (meta (first types)) {})]
    (loop [a accum
           t (first real-types)
           fields (second real-types)
           next-t (next (next real-types))]
      (if-not (nil? t)
        (let [recursive (get-recursive t)]
          (recur (-> a
                     (conj-type t default recursive)
                     (conj-fields t fields default recursive))
                 (first next-t)
                 (second next-t)
                 (next (next next-t))))
        a))))

(defn ^:private parse-type-groups
  [accum type-groups]
  (reduce parse-types accum type-groups))

(def ^:private primitive-types
  (mapv (fn [i]
          {:db/id (get-temp-id! i)
           :node/type :type
           :type/name (str i)
           :type/kebab-case-name (->kebab-case-keyword i)
           :type/camelCaseName (->camelCaseKeyword i)
           :type/PascalCaseName (->PascalCaseKeyword i)
           :type/snake_case_name (->snake_case_keyword i)
           :type/nature :primitive})
        '[String Float Integer Boolean DateTime ID]))

(defn ^:private internal-schema
  [source-schemas]
  (parse-type-groups primitive-types source-schemas))

;;TODO
(defn ^:private is-schema-valid?
  [schema]
  true)

(defn ^:private ensure-meta-db
  [schema]
  #_(clojure.pprint/pprint schema)
  (let [conn (d/create-conn meta-schema)]
    (d/transact! conn schema)
    conn))

(defn ^:private extend-meta-db
  [conn schema]
  #_(clojure.pprint/pprint schema)
  (d/transact! conn schema)
  conn)

(defn name-str [& xs]
  (->> (map #(if (ident? %) (name %) (str %)) xs)
       (apply str)))

(defn join-ns [namespacee namee]
  (assert (every? (complement #{""}) (map str [namespacee namee])))
  (keyword (name-str namespacee) (name-str namee)))

(defn ^:private default-prefix []
  (str (ns-name *ns*)))

(def primitive-names
  (set (map :type/kebab-case-name primitive-types)))

(defn primitive? [t]
  (and (contains? primitive-names (:type/kebab-case-name t))
       (= :type (:node/type t))))

(defn ^:private qualified-names-tx [db]
  (let [entities (d/q '[:find [(pull ?e [:db/id
                                         :ns-prefix/tag
                                         :node/type
                                         :type/kebab-case-name
                                         :param/kebab-case-name
                                         :field/kebab-case-name
                                         {:field/parent [:type/kebab-case-name]}
                                         {:param/parent [:field/kebab-case-name
                                                         {:field/parent
                                                          [:type/kebab-case-name]}]}])
                               ...]
                        :where [?e :node/type]]
                      db)]

    (->> entities
         (remove primitive?)
         (mapv (fn [{prefix :ns-prefix/tag
                     field-name :field/kebab-case-name
                     type-name :type/kebab-case-name
                     param-name :param/kebab-case-name
                     {field-parent-name :type/kebab-case-name} :field/parent
                     {{param-gparent-name :type/kebab-case-name} :field/parent
                      param-parent-name :field/kebab-case-name} :param/parent
                     db-id :db/id
                     :as x
                     :or {prefix (default-prefix)}}]
                 (let [ent {:db/id db-id
                            :ns-prefix/tag prefix}]
                   (cond
                     field-name
                     (assoc ent :field/qualified-name
                            (join-ns (name-str prefix "." field-parent-name)
                                     field-name))


                     param-name
                     (assoc ent :param/qualified-name
                            (join-ns (name-str  prefix "."
                                                param-gparent-name "."
                                                param-parent-name)
                                     param-name))

                     type-name
                     (assoc ent :type/qualified-name (join-ns prefix type-name)))))))))

(comment



  (let [meta-db
        (init-schema
         '[^{:ns-prefix/tag-recursive :foo}
           myType
           [my-id name nested [param]]])

        tx (->> (qualified-names-tx @meta-db)
                (map #(dissoc % :db/id :ns-prefix/tag)))]
    (= (set tx)
       #{{:field/qualified-name :foo.my-type/name}
         {:param/qualified-name :foo.my-type.nested/param}
         {:field/qualified-name :foo.my-type/nested}
         {:field/qualified-name :foo.my-type/my-id}
         {:type/qualified-name :foo/my-type}}))

  {:field/qualified-name :foo.tx/amount}
  {:type/qualified-name :foo/tx}
  {:param/qualified-name :foo.tx.nested/param}
  {:field/qualified-name :foo.tx/nested}


  (def meta-db
    (engine/init-schema
     '[^{:spec/tag-recursive true
         :datomic/tag-recursive true
         :json-serde/tag-recursive true
         :ns-prefix/tag-recursive :foo}
       tx
       [^Integer amount]]))

  (hodur-spec/defspecs meta-db) ;=> [:foo.tx/amount :foo/tx]

  (def parse-json
    (hodur-json/parser meta-db :tx))


  (parse-json "{\"amount\":10}") ;=> {:foo.tx/amount 10}


  (def schema
    (hodur-datomic/schema meta-db))
  ;; =>
  [#:db{:ident :foo.tx/amount,
        :valueType :db.type/long,
        :cardinality :db.cardinality/one}]






  (let [meta-db
        (init-schema
         '[
           [my-id name nested [param]]])

        tx (->> (qualified-names-tx @meta-db)
                (map #(dissoc % :db/id)))]
    tx
    #_(= (set tx)
       #{{:field/qualified-name :foo.my-type/name}
         {:param/qualified-name :foo.my-type.nested/param}
         {:field/qualified-name :foo.my-type/nested}
         {:field/qualified-name :foo.my-type/my-id}
         {:type/qualified-name :foo/my-type}}))

  (let [meta-db
        (init-schema
         '[^{:prefix/tag-recursive :foo}
           myType
           [^ID my-id ^String name nested [^{:prefix/tag :wat} param]]])

        tx (->> (enrich-names-tx @meta-db)
                (map #(dissoc % :db/id)))]
    tx
    #_(= tx [{:field/qualified-name :foo.my-type/name}
           {:param/qualified-name :foo.my-type.nested/param}
           {:field/qualified-name :foo.my-type/nested}
           {:field/qualified-name :foo.my-type/my-id}
             {:type/qualified-name :foo/my-type}]))

  #:field{:qualified-name :foo.my-type/name}
  ;; Should the wat here be
  #:param{:qualified-name :wat.my-type.nested/param}
  #:field{:qualified-name :foo.my-type/nested}
  #:field{:qualified-name :foo.my-type/my-id}
  #:type{:qualified-name :foo/my-type}

  (map #(dissoc % :db/id) xs)

  (map primitive? xs)

  (remove primitive? xs)


  (def meta-db
    (init-schema
     '[^{:prefix/tag-recursive :pgo}
       tx
       [^Integer money ^String cpf foo [bar]]]))

  (def meta-db
    (init-schema
     '[^{:prefix/tag-recursive :pgo}
       tx
       [foo [bar]]]))

  (def meta-db
    (init-schema
     '[^{:prefix/tag :pgo}
       default

       tx
       [^Integer money ^{:type String
                         :prefix/tag false} cpf]]))


  (d/q '{:find [(pull ?e [:prefix/tag-recursive :prefix/tag :field/name :type/name *])]
         :where [[?e :prefix/tag]]}
       @meta-db)

  (dbg/a>>)

  (dbg/nuke)



  )
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Public functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn extend-schema [conn source-schema & others]
  (reset-temp-id-state!)
  (let [source-schemas (conj others source-schema)
        schema (parse-type-groups [] source-schemas)]
    (if (is-schema-valid? schema)
      (extend-meta-db conn schema))))

(defn init-schema [source-schema & others]
  (reset-temp-id-state!)
  (let [source-schemas (conj others source-schema)
        schema (internal-schema source-schemas)]
    (if (is-schema-valid? schema)
      (ensure-meta-db schema))))

#?(:clj
   (defn init-path [path & others]
     (let [paths (-> others flatten (conj path) flatten)]
       (->> paths
            schema-streams
            slurp-files
            (apply init-schema)))))

#_(let [datomic-c (init-path "test/schemas/several/datomic"
                             "test/schemas/several/shared")]
    (clojure.pprint/pprint
     (map #(cond-> {}
             (:type/name %) (assoc :type (:type/name %))
             (:field/name %) (assoc :field (:field/name %))
             (:param/name %) (assoc :param (:param/name %)))
          (d/q '[:find [(pull ?e [*]) ...]
                 :where
                 [?e :datomic/tag true]]
               @datomic-c))))

#_(let [#_lacinia-c #_(init-path "test/schemas/several/lacinia"
                                 "test/schemas/several/shared")
        datomic-c (init-path "test/schemas/several/datomic"
                             "test/schemas/several/shared")]
    #_(clojure.pprint/pprint
       (d/q '[:find [(pull ?e [*]) ...]
              :where
              [?e :datomic/tag true]]
            @datomic-c)))

#_(clojure.pprint/pprint
   (d/q '[:find [(pull ?e [* {:field/_parent [*]}]) ...]
          :where
          [?e :type/name]
          [?e :type/nature :user]]
        @(init-schema '[A [^{:type String}
                           b]])))
