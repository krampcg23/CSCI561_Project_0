;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; STARTER DEFINITIONS FOR FINITE AUTOMATA ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Authors: Matthew Baldin, Clayton Kramp, Hunter Johnson

;; A structure type for finite automata
(defstruct (finite-automaton)
  "A Finite Automaton."
  ;; list of states
  (states nil :type list)
  ;; list of alphabet symbols
  (alphabet nil :type list)

  ;; edge list,
  ;; each element is a list (predecessor-state input-symbol successor-state)
  (edges nil :type list)

  ;; start state
  start

  ;; list of accept states
  (accept nil :type list))

(defun make-fa (edges start accept)
  "Convenience constructor for finite automata"
  (let ((state-hash (make-hash-table :test #'equal))
        (alphabet-hash (make-hash-table :test #'equal)))
    ;; Prime state set
    (setf (gethash start state-hash) t)
    (dolist (a accept)
      (setf (gethash a state-hash) t))
    ;; Collect states and alphabet from edges
    (loop for (q0 e q1) in edges
       do (setf (gethash q0 state-hash) t
                (gethash e alphabet-hash) t
                (gethash q1 state-hash) t))
    ;; Result
    (make-finite-automaton
     :states (loop for k being the hash-key in state-hash collect k)
     :alphabet (loop for k being the hash-key in alphabet-hash collect k)
     :start start
     :accept accept
     :edges edges)))

(defun dot-symbol (thing)
  "Pretty-print greek letters for Graphviz output"
  (case thing
    (:alpha "&alpha;")
    (:beta "&beta;")
    (:gamma "&gamma;")
    (:delta "&delta;")
    (:epsilon "&epsilon;")
    (:zeta "&zeta;")
    (:eta "&eta;")
    (:theta "&theta;")
    (:iota "&iota;")
    (:kappa "&kappa;")
    (:lambda "&lambda;")
    (:mu "&mu;")
    (:nu "&nu;")
    (:xi "&xi;")
    (:omicron "&omicron;")
    (:pi "&pi;")
    (:rho "&rho;")
    (:sigma "&sigma;")
    (:tau "&tau;")
    (:upsilon "&upsilon;")
    (:phi "&phi;")
    (:chi "&chi;")
    (:omega "&omega;")
    (t thing)))


;; Example:
;;
;; (fa-dot (make-fa '((q-even 0 q-even)
;;                    (q-even 1 q-odd)
;;                    (q-odd 1 q-even)
;;                    (q-odd 0 q-odd))
;;                  'q-even
;;                  '(q-odd))
;;         "/tmp/cs561-project-1-example.dot")
(defun fa-dot (fa place)
  "Output a Graphviz dot file for finite automata"
  (let ((hash (make-hash-table :test #'equal)))
    ;; number the states
    (loop for i from 0
       for q in (finite-automaton-states fa)
       do (setf (gethash q hash) i))
    (labels ((state-number (state)
               (gethash state hash))
             (helper (stream)
               ;; output
               (Format stream "~&digraph { ~%")
               ;; state labels
               (format stream "~:{~&  ~A[label=\"~A\"];~}"
                       (map 'list (lambda (state)
                                    (list (state-number state)
                                          state))
                            (finite-automaton-states fa)))
               ;; start shape
               (format stream "~&  start[shape=none];")
               (format stream "~&  start -> ~A;"
                       (state-number (finite-automaton-start fa)))
               ;; accept state
               (format stream "~:{~&  ~A [ shape=~A ];~}"
                       (map 'list (lambda (q)
                                    (list (state-number q) "doublecircle"))
                            (finite-automaton-accept fa)))
               ;; edges
               (loop for (q0 e q1) in (finite-automaton-edges fa)
                  do (format stream "~&  ~A -> ~A [fontsize=~D,label=\"~A\"];~%"
                             (state-number q0)
                             (state-number q1)
                             12 (dot-symbol e)))
               ;; end
               (format stream "~&}~%")))
      (cond
        ((streamp  place)
         (helper place))
        ((eq place t)
         (helper *standard-output*))
        ((or (stringp place)
             (pathnamep place))
         (with-open-file (stream place
                                 :direction :output
                                 :if-exists :supersede
                                 :if-does-not-exist :create)
         (helper stream)))
        (t (error "Unrecognized output type: ~A" place))))))

;; SBCL-specific function to generate a PDF of the FA
;;
;; Example:
;;
;; (fa-pdf (make-fa '((q-even 0 q-even)
;;                    (q-even 1 q-odd)
;;                    (q-odd 1 q-even)
;;                    (q-odd 0 q-odd))
;;                  'q-even
;;                  '(q-odd))
;;         "/tmp/cs561-project-1-example.pdf")
#+sbcl
(defun fa-pdf (fa pathname)
  (with-input-from-string (input (with-output-to-string (stream)
                                     (fa-dot fa stream)))
    (with-open-file (output pathname :direction :output :if-exists :supersede)
      (sb-ext:run-program "dot" (list "-Tpdf")
                          :search t
                          :wait t
                          :input input
                          :output output))))



(defun state-predicate-atom (a b)
  "Predicate to order states, atom case."
  (etypecase a
    ((or symbol string)
     (etypecase b
       ((or symbol string)
        (string-lessp a b))
       (number nil)))
    (number
     (etypecase b
       ((or symbol string)
        t)
       (number (<= a b))))))

(defun state-predicate (a b)
  "Predicate to order states."
  (etypecase a
    (atom (etypecase b
            (atom (state-predicate-atom a b))
            (list t)))
    (cons (etypecase b
            (atom nil)
            (cons (if (equal (car a) (car b))
                      (state-predicate (cdr a)
                                       (cdr b))
                      (state-predicate (car a)
                                       (car b))))))))

(defun newstate ()
  "Construct a unique state for a finite automaton."
  (gensym "q-"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; COMPLETE THE FUNCTIONS BELOW ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Convert a regular expression to a nondeterministic finite automaton
;;
;; The following are examples of possible regular expression arguments to this function:
;;
;; - (:concatenation a b c)
;; - (:union a b c)
;; - (:kleene-closure a)
;; - (:concatenation (:union a b) (:kleene-closure c))

(defun regex->nfa (regex)
  (labels ((rec (x regex)
             (destructuring-bind (edges start) x
               ;; Base Case
               (typecase regex
                 (symbol
                  (let* ((accept (newstate))
                         (edge (list start regex accept))
                         (edges (cons edge edges)))
                    (list edges accept)))
                 (list
                  (ecase (car regex)
                    (:concatenation
                     (reduce #'rec (cdr regex) :initial-value x))
                    
                    (:union
                     (let* ((accept (newstate)))
                       (dolist (child (cdr regex))
                         (let* ((edgeList (list edges start))
                                (output (rec edgeList child)))
                           (destructuring-bind (edges1 accept1) output
                             (let* ((edge (list accept1 :epsilon accept)))
                               (setq edges (cons edge edges1))))))
                       (list edges accept)))
                    
                    (:kleene-closure
                     (let* ((start1 (newstate)))
                            (let* ((newX (list edges start1)))
                              (destructuring-bind (newEdges accept) (rec newX (cadr regex))
                                (let* ((edge1 (list start :epsilon start1))
                                       (edge2 (list start :epsilon accept))
                                       (edge3 (list accept :epsilon start1))
                                       (newEdges (cons edge3 newEdges))
                                       (newEdges (cons edge2 newEdges))
                                       (newEdges (cons edge1 newEdges)))
                                  (list newEdges accept))))))
                    ))
                 ))))
    (let* ((start (newstate)))
      (destructuring-bind (edges accept) (rec (list nil start) regex)
        (make-fa edges start (list accept))))))



(defun eps-closure (nfa unvisited initial-closure)

  (labels ((func (q)
             (let* ((output '()))
               (dolist (edge (finite-automaton-edges nfa) output)
                 (if (and (equal (car edge) q) (equal (cadr edge) :epsilon))
                    (setf output (cons (car (cdr (cdr edge))) output))))
               output))
           (visit (c q)
             (if (member q c :test 'equal)
                 c
                 (eps-closure nfa (func q) (cons q c)))))
             
    (let* ((C1 (reduce #'visit unvisited :initial-value initial-closure)))
      C1)
    ))


(defun move-eps-closure(nfa initial-states transition)
  (labels (
           (func (q)
             (let* ((output '()))
               (dolist (edge (finite-automaton-edges nfa) output)
                 (if (and (equal (car edge) q) (equal (cadr edge) transition))
                     (setf output (cons (car (cdr (cdr edge))) output))))
               output))
           (visit (c q)
             (eps-closure nfa (func q) c)))
    (let* ((C1 (reduce #'visit (eps-closure nfa initial-states '()) :initial-value '())))
      C1
      )))

;; Convert a nondeterministic finite automaton to a deterministic
;; finite automaton
;;
(defun nfa->dfa (nfa)
  (let ((visited-hash (make-hash-table :test #'equal))
        (alphabet (remove :epsilon (finite-automaton-alphabet nfa))))
    (labels ((constructF (accepts)
               (let* ((output '())
                      (added '()))
                 (loop for key being the hash-keys of visited-hash do
                       (dolist (item accepts output)
                         (if (and (member item key :test 'equal) (not (member key added :test 'equal)))
                             (progn
                               (setf added (cons key added))
                               (setf output (cons key output))))))
                 (setq output (sort-state output))
                 output))

             (sort-state (u)
               (sort u #'state-predicate))
             (visit-state (edges subset)
               (labels ((visit (edges subset)
                          (setf (gethash subset visited-hash) t)
                          (reduce #'visit-symbol alphabet :initial-value edges))
                        (visit-symbol (edges sigma)
                          (let* ((u1 (move-eps-closure nfa subset sigma)))
                            (if (not (equal u1 '()))
                                (progn
                                 ; (print subset)
                                 ; (print u1)
                                  (visit-state (cons (list subset sigma u1) edges) u1))
                                edges)
                            )))
                 (setf subset (sort-state subset))
                 (if (gethash subset visited-hash)
                     edges
                     (visit edges subset))
                 )))
      (let* ((q01 (eps-closure nfa (list (finite-automaton-start nfa)) '())))
        (setq q01 (sort-state q01))
        (let* (
               (E1 (visit-state '() q01))
               (F1 (constructF (finite-automaton-accept nfa))))
      (make-fa E1 q01 F1))
      ))))

 

;tried adding back epsilon edges to start from all previous - does not work
;try making an epsilon edge between all of the previous start states
;will need to modify accept state
(defun reverse-dfa (dfa)
  (let* (
         (output '()))
    (dolist (edge (finite-automaton-edges dfa) output)
      (setf output (cons (reverse edge) output)))
    (let* ((head (car (finite-automaton-accept dfa))))
      (dolist (state (finite-automaton-accept dfa) output)
        (setq output (cons (list head :epsilon state) output))))
      (make-fa output (car (finite-automaton-accept dfa)) (list (finite-automaton-start dfa)))
  ))
           
;; Minimize the states in the dfa
(defun dfa-minimize (dfa)                                        ; (
 ( let* ((newDFA (nfa->dfa (reverse-dfa (nfa->dfa (reverse-dfa dfa))))))
    newDFA)
  )

(defun product-dfa (dfa-0 dfa-1 accepts)
  (let* ((edges '())
         (start (list (finite-automaton-start dfa-0) (finite-automaton-start dfa-1))))
    (dolist (a (finite-automaton-edges dfa-0) edges)
      (dolist (b (finite-automaton-edges dfa-1) edges)
        (let* ((head (list (car a) (car b)))
               (foot (list (car (cdr (cdr a))) (car (cdr (cdr b)))))
               (e0 (cadr a))
               (e1 (cadr b)))
          (if (equal e0 e1)
              (setq edges (cons (list head e0 foot) edges))))))
    (make-fa edges start accepts)))

(defun dfa-intersection (dfa-0 dfa-1)
  (let* ((accepts '()))
    (dolist (a (finite-automaton-accept dfa-0) accepts)
      (dolist (b (finite-automaton-accept dfa-1) accepts)
        (setq accepts (cons (list a b) accepts))))
    (product-dfa dfa-0 dfa-1 accepts))
  )

(defun dfa-cartesian (dfa-0 dfa-1 accepts)
  (let* ((edges '())
         (start (list (finite-automaton-start dfa-0) (finite-automaton-start dfa-1))))
    (dolist (a (finite-automaton-edges dfa-0) edges)
      (dolist (b (finite-automaton-edges dfa-1) edges)
        (let* ((head (list (car a) (car b)))
               (foot (list (car (cdr (cdr a))) (car (cdr (cdr b)))))
               (e0 (cadr a))
               (e1 (cadr b)))
          (setq edges (cons (list head (list e0 e1) foot) edges)))))
    (make-fa edges start accepts)))

;;;;;;;;;;;;;;;;;;;;;;
;;;; EXTRA CREDIT ;;;;
;;;;;;;;;;;;;;;;;;;;;;

;; ;; Return the complement of FA
;; (defun fa-complement (fa ))

;; ;; Test whether two FA are equivalent
;; (defun fa-equivalent (fa-0 fa-1))

;; ;; Test whether FA-0 is subseteq of FA-1
;; (defun fa-subseteq (fa-0 fa-1))

;;;;;;;;;;;;;;;complement;;;;;;;;;

(defun does-state-have-alphabet-edge (edges symbol state)
  (let* ((does-edge-exist nil))
    (dolist (edge edges)
      (if (and
           (equal state (car edge))
           (equal symbol (cadr edge)))
          (setq does-edge-exist T)
          nil
          )
      )
    does-edge-exist
    )
  )

(defun add-dead-state-edges (fa)
  (let* ((dead-state (newstate))
         (edges (finite-automaton-edges fa)))
    (dolist (state (finite-automaton-states fa))
      (dolist (symbol (finite-automaton-alphabet fa))
        (if (not (does-state-have-alphabet-edge edges symbol state))
            (setq edges (cons (list state symbol dead-state) edges))
            nil
            )
        )
      )
    (dolist (symbol (finite-automaton-alphabet fa))
      (setq edges (cons ( list dead-state symbol dead-state) edges))
      )
    (make-fa edges (finite-automaton-start fa) (finite-automaton-accept fa))
    )
  )

(defun flip-accept-and-non-accept (fa) 
  (let* ((list-of-new-accept-states nil)
         (possible-new-dead '(dead)))
    (setq list-of-new-accept-states 
          (set-difference 
           (finite-automaton-states fa)
           (finite-automaton-accept fa)
           ))
    (if (not (finite-automaton-alphabet fa))
        (setq list-of-new-accept-states 
              (cons (car list-of-new-accept-states) possible-new-dead))
        nil
        )
    (make-fa 
     (finite-automaton-edges fa) 
     (finite-automaton-start fa) 
     list-of-new-accept-states) 
    )
  )

(defun fa-complement (fa)
  (setq fa
        (add-dead-state-edges fa))
  (setq fa 
        (flip-accept-and-non-accept fa))
  fa
  )



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;equal and subseteq;;;;;;;;;;;;


(defun get-list-of-edges-to-process (state edges)
  (let* ((edges-with-state nil))
    (dolist (edge edges)
      (if (equal (car edge) state)
          (setq edges-with-state (cons edge edges-with-state))
          )
      )
    edges-with-state
    )
  )

(defun bfs (edges visited-map state-to-process)
  (setf (gethash state-to-process visited-map) t)
  (dolist (edge-to-process 
           (get-list-of-edges-to-process state-to-process edges))
    (if (not (gethash (caddr edge-to-process) visited-map))
        (bfs edges visited-map (caddr edge-to-process))
        nil
        )
    )
  )


(defun is-state-accept (state accept-list)
  (let* ((is-in-accept NIL))
    (dolist (accept-state accept-list)
      (if (equal (symbol-name state) (symbol-name accept-state))
          (setq is-in-accept T)
          nil
          )
      )
    is-in-accept)
  )

(defun accept-state-finder (edge0 edge1 accept-list-0 accept-list-1 end-state-classifier)
  (let* ((result nil))
    (if (funcall end-state-classifier 
         (is-state-accept edge0 accept-list-0)
         (is-state-accept edge1 accept-list-1))
        (setq result T)
      NIL)
    result
    )
  )

(defun new-combined-state (a b)
  (make-symbol (concatenate 'string (write-to-string a)  "," (write-to-string b))))

(defun evaluate-hash-map-and-accept (visited-map accept-states)
  (let* ((did-accept-state-get-visited nil))
    (dolist (accept-state accept-states)
      (if (gethash accept-state visited-map)
          (setq did-accept-state-get-visited T)
          nil
          )
      )
    (not did-accept-state-get-visited)
    )
  )


(defun init-hash-map-with-states (hash-map list-of-states)
  (dolist (state list-of-states)
    (setf (gethash state hash-map) nil)
    )
  )


(defun create-list-of-product-states (dfa-0 dfa-1)
  (let* ((product-states NIL))
  (dolist (state-0 (finite-automaton-states dfa-0))
    (dolist (state-1 (finite-automaton-states dfa-1))
      (setq product-states 
            (cons 
             (new-combined-state state-0 state-1)
             product-states))
      )
    )
  product-states)
)

(defun return-proper-state (state-to-find list-of-states)
  (let* ((state-to-return nil))
    (dolist (current-state list-of-states)
      (if (equal (write-to-string current-state) (write-to-string state-to-find))
          (setq state-to-return current-state)
        nil)
      )
    state-to-return
    )
  )

(defun is-fa-empty (fa)
  (let* ((states-map (make-hash-table :test #'equal)))
    (init-hash-map-with-states states-map (finite-automaton-states fa))
    (bfs (finite-automaton-edges fa) states-map (finite-automaton-start fa))
    (evaluate-hash-map-and-accept states-map (finite-automaton-accept fa))
    )
  )

(defun dfa-product-hunter (dfa-0 dfa-1 end-state-classifier)
  (let* ((product-dfa-edges NIL)
         (start-state NIL)
         (end-states NIL)
         (states-list (create-list-of-product-states dfa-0 dfa-1)))
    (format t "~%in dfa product ~%")
    (dolist (dfa-0-edge (finite-automaton-edges dfa-0))
      (dolist (dfa-1-edge (finite-automaton-edges dfa-1))
        (if (equal (cadr dfa-0-edge) (cadr dfa-1-edge))
            (let* ((new-first-state (return-proper-state (new-combined-state (car dfa-0-edge) (car dfa-1-edge)) states-list))
                   (new-last-state  (return-proper-state (new-combined-state (caddr dfa-0-edge) (caddr dfa-1-edge)) states-list)))
              (if (and
                   (equal (car dfa-0-edge) (finite-automaton-start dfa-0))
                   (equal (car dfa-1-edge) (finite-automaton-start dfa-1)))
                  (setq start-state new-first-state)
                  nil)
              (if (accept-state-finder 
                   (car dfa-0-edge) 
                   (car dfa-1-edge) 
                   (finite-automaton-accept dfa-0) 
                   (finite-automaton-accept dfa-1)
                   end-state-classifier)
                  (if (not (is-state-accept new-first-state end-states))
                      (setq end-states (cons new-first-state end-states))
                      nil)
                  nil)
              (let* ((new-cross-edge
                       (list
                        new-first-state
                        (cadr dfa-0-edge)
                        new-last-state
                        )))
                (setq product-dfa-edges (cons new-cross-edge product-dfa-edges))
                )
              )
            nil)
        )
      )
    (make-fa product-dfa-edges start-state end-states)
    )
  )


(defun xor (cond1 cond2)
  (or(equal cond1 (not cond2))(equal (not cond1) cond2))
  )


(defun fa-equivalent (fa-0 fa-1)
  (is-fa-empty (dfa-product-hunter (nfa->dfa fa-0) (nfa->dfa fa-1) #'xor))
  )

(defun a-not-b (cond1 cond2)
  (and cond1 (not cond2))
  )

;; ;; Test whether FA-0 is subseteq of FA-1
(defun fa-subseteq (fa-0 fa-1)
  (is-fa-empty (dfa-product-hunter (nfa->dfa fa-0) (nfa->dfa fa-1) #'a-not-b))
  )

