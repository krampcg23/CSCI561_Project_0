;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; STARTER DEFINITIONS FOR FINITE AUTOMATA ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defun new-combined-state (a b)
  (make-symbol (concatenate 'string (symbol-name a)  "," (symbol-name b))))

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
      ;  (format t "~% The edges are:  ~%")
      ;  (princ edges)
      ;  (format t "~% The accepts are ~%")
      ;  (princ (list accept))
        (make-fa edges start (list accept))))))



(defun eps-closure(nfa unvisited start)
  (labels ((makeP (nfa q)
             (let* ((edges (finite-automaton-edges nfa))
                    (p '()))
               (dolist (edge edges p)
                 (if (equal q (car edge))
                     (if (equal :epsilon (cadr edge))
                           (push (car (cdr (cdr edge))) p)
                           )))))
             
           (closure (nfa q c)
             (let* ((p (makeP nfa q)))
               (eps-closure nfa p c)               
               ))
           
           (visit (c q)
             (if (not c)
                 (closure nfa q (list q))
                 (if (member q c)
                     c
                     (closure nfa q (cons q c))
                         ))))
    (if (equal nil unvisited)
        start)
    (let* ((c1 (reduce #'visit unvisited :initial-value start)))
      c1)
    ))


(defun move-eps-closure(nfa q transition)
  (labels ((makeP (nfa q transition)
                 (let* ((p '())
                        (edges (finite-automaton-edges nfa)))
                   (dolist (edge edges p)
                     (typecase (car edge)
                       (list
                        (if (member q (car edge))
                            (if (equal transition (cadr edge))
                                (push (car (cdr (cdr edge))) p))))
                       (t
                        (if (equal q (car edge))
                            (if (equal transition (cadr edge))
                                (push (car (cdr (cdr edge))) p)))))
                     )))
           (visit (c q)
             (let* ((p (makeP nfa q transition)))
               (eps-closure nfa p c))))
    (let* ((c1 (reduce #'visit (eps-closure nfa q '()) :initial-value '())))
      c1)
    )
)

;; Convert a nondeterministic finite automaton to a deterministic
;; finite automaton
;;
(defun nfa->dfa (nfa)
  (let* ((visited-hash (make-hash-table :test #'equal))
        (Q1 '())
        (alphabet (remove :epsilon (finite-automaton-alphabet nfa))))
    (labels (
             (denest (list)
               (cond ((null list) nil)
                     ((atom (car list)) (cons (car list) (denest (cdr list))))
                     (t (append (denest (car list)) (denest (cdr list))))))
             
             (makeStart (listOfStates)
               (if (equal 1 (length listOfStates))
                   (setq listOfStates (car listOfStates)))
               listOfStates)
             
             (sort-state (u)
               (sort u #'state-predicate))
             (visit-state (edges subset) ; visit-state(e, u)
               (labels ((visit-symbol (edges transition)
                          (let* ((u1 (move-eps-closure nfa subset transition)))
                            (if (equal u1 nil)
                                edges
                                (progn
                                  (let* ((start (makeStart subset))
                                         (u1New (makeStart u1))
                                         (edge (list start transition u1New)))
                                    (setq u1 (denest u1))
                                    (setq u1 (remove-duplicates u1))
                                    (setq u1 (sort-state u1))
                                    (setq edges (push edge edges))
                                    (visit-state edges u1))))))
                        (visit (edges subset) ; else case
                          (setq subset (denest subset))
                          (setq subset (remove-duplicates subset))
                          (setq subset (sort-state subset))
                          (setf (gethash subset visited-hash) t)
                          (push subset Q1)
                          (reduce #'visit-symbol alphabet :initial-value edges)))
                 (setq subset (denest subset))
                 (setq subset (remove-duplicates subset))
                 (setq subset (sort-state subset))
                 (if (gethash subset visited-hash)
                     edges   ;true, then return e
                     (visit edges subset))))) ;else go to the else case visit

      (let* (
             (q01 (eps-closure nfa (list (finite-automaton-start nfa)) '()))
             (q01 (denest q01))
             (q01 (remove-duplicates q01))
             (q01 (sort-state q01))
             (E1 (visit-state '() q01))
             (accepts (denest (finite-automaton-accept nfa)))
             (accepts (remove-duplicates accepts))
             (accepts (sort-state accepts))
             (F1 (remove-if (lambda (state) (not (intersection state accepts :test 'equal))) Q1))
             (q01 (makeStart q01))
             ;(F1 (makeStart F1))
             )
        (Make-fa E1 q01 F1)))))
                             

;;;;;;;;;;;;;;;;;;;;;Intersection code;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun dfa-intersection (dfa-0 dfa-1)
  (dfa-product dfa-0 dfa-1 #'binary-and)
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

(defun binary-and (arg0 arg1)
  (and arg0 arg1)
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
      (if (equal (symbol-name current-state) (symbol-name state-to-find))
          (setq state-to-return current-state)
        nil)
      )
    state-to-return
    )
  )

;;Output a list of edges that corespond to the product dfa
(defun dfa-product (dfa-0 dfa-1 end-state-classifier)
  (let* ((product-dfa-edges NIL)
         (start-state NIL)
         (end-states NIL)
         (states-list (create-list-of-product-states dfa-0 dfa-1)))
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

;;TEST FUNCTIONS;;
(defun output-all-dot-files-for-intersection (dot-file-path)
  (test-dfa-product-simple 
   dot-file-path)
  (test-dfa-product-three-state 
   dot-file-path)
  (test-dfa-product-nil 
   dot-file-path )
  (test-dfa-intersection-simple 
   dot-file-path)
  (test-dfa-intersection-nil 
   dot-file-path)
  (make-dot-file-three-state-dfa-1 
   dot-file-path)
  (make-dot-file-three-state-dfa-2 
   dot-file-path)
  (test-dfa-intersection-three-state 
   dot-file-path)
  )
(defun test-dfa-product-simple (dot-file-path) 
  (fa-dot
   (dfa-product 
    (make-fa '((a 1 b)
               (a 0 a)
               (b 0 a)
               (b 1 a))
             'a
             '(b))
    (make-fa '((c 1 c)
               (c 0 d)
               (d 0 d)
               (d 1 c))
             'c
             '(d))
    #'equal
    )
   (concatenate 'string dot-file-path "test_product_dfa_simple.dot")
   )
  )

(defun test-dfa-product-three-state (dot-file-path)
  (fa-dot
   (dfa-product
    (make-three-state-dfa-1)
    (make-three-state-dfa-2)
    #'equal
    )
   (concatenate 'string dot-file-path "test_dfa_product_three_state.dot")
   )
  )

(defun dot-file-path ()
     "C:\\Users\\Hunter Johnson\\Documents\\CSCI561\\project1DotFiles\\"
  )

(defun test-dfa-product-nil(dot-file-path)
  (fa-dot
   (dfa-product 
    (make-fa '()
             nil
             '())
    (make-fa '((c 1 c)
               (c 0 d)
               (d 0 d)
               (d 1 c))
             'c
             '(d))
    #'equal
    )
   (concatenate 'string dot-file-path "test_dfa_product_nil.dot")
   )
  )

(defun test-dfa-intersection-simple (dot-file-path)
  (fa-dot
   (dfa-intersection
    (make-fa '((a 1 b)
               (a 0 a)
               (b 0 a)
               (b 1 a))
             'a
             '(b))
    (make-fa '((c 1 c)
               (c 0 d)
               (d 0 d)
               (d 1 c))
             'c
             '(c))
    )
   (concatenate 'string dot-file-path "test-intersection-dfa.dot")
   )
  )

(defun test-dfa-intersection-nil(dot-file-path)
  (fa-dot
   (dfa-intersection 
    (make-fa '()
             nil
             '())
    (make-fa '((c 1 c)
               (c 0 d)
               (d 0 d)
               (d 1 c))
             'c
             '(d))
    )
   (concatenate 'string dot-file-path "test_dfa_intersection_nil.dot")
   )
  )

(defun make-three-state-dfa-1 ()
      (make-fa '((a 3 d)
               (a 1 b)
               (d 2 b)
               (d 1 d)
               (b 1 b))
             'b
             '(d b))
  )

(defun make-dot-file-three-state-dfa-1(dot-file-path)
    (fa-dot
   (make-three-state-dfa-1)
   (concatenate 'string dot-file-path "three-state-dfa-1.dot")
   )
  )


(defun make-three-state-dfa-2()
  (make-fa '(
             (a 1 b)
             (a 3 a)
             (b 2 c)
             (c 1 c)
             (c 4 a))
           'c
           '(c))
  )

(defun make-dot-file-three-state-dfa-2(dot-file-path)
    (fa-dot
   (make-three-state-dfa-2)
   (concatenate 'string dot-file-path "three-state-dfa-1.dot")
   )
  )

(defun test-dfa-intersection-three-state (dot-file-path)
  (fa-dot
   (dfa-intersection
    (make-three-state-dfa-1)
    (make-three-state-dfa-2)
    )
   (concatenate 'string dot-file-path "dfa-intersection-three-state.dot")
   )
  )

(defun make-fa-no-edges()
    (make-fa '()
           'c
           '(a))
  )

(defun print-fa-no-edges (dot-file-path)
  (fa-dot
    (make-fa-no-edges)
   (concatenate 'string dot-file-path "fa-no-edges.dot")
   )
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;end of functions for intersection;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun reverseDFA (dfa)
  (labels ((reverseEdges (edges)
             (let* ((reversedEdges '() ))
               (dolist (edge edges reversedEdges)
                 (let* ((start (car (cdr (cdr edge))))
                        (finish (car edge))
                        (transition (cadr edge))
                        (reversedEdge (list start transition finish)))
                   (push reversedEdge reversedEdges)))
               reversedEdges))
           
           (constructExtraEdges (start accepts)
             (let* ((extraEdges '() ))
               (dolist (accept accepts extraEdges)
                 (let* ((edge (list start :epsilon accept)))
                      ;  (otherEdge (list accept :epsilon start)))
                   (push edge extraEdges))
                   ;(push otherEdge extraEdges))
               extraEdges)))

           (combineEdges (edges1 edges2)
             (let* ((edges '()))
               (dolist (edge edges1 edges)
                 (push edge edges))
               (dolist (edge edges2 edges)
                 (push edge edges))
               edges)
             ))
    
    (let* ((q01 (newstate))
           ;(states (cons q01 (finite-automaton-states dfa)))
           (accept (list (finite-automaton-start dfa)))
           (edges '())
           (reversedEdges (reverseEdges (finite-automaton-edges dfa)))
           (newStartToOldAccept (constructExtraEdges q01 (finite-automaton-accept dfa))))
      (setq edges (combineEdges reversedEdges newStartToOldAccept))
      (make-fa edges q01 accept)
    )))
           
;; Minimize the states in the dfa
(defun dfa-minimize (dfa)                                        ; (
 ( let* ((newDFA (nfa->dfa (reverseDFA (nfa->dfa (reverseDFA dfa))))))
    newDFA)
  )

(defun test-regex->nfa ()
  (fa-dot 
   (regex->nfa '(:concatenation a b (:kleene-closure c)))
    "C:\\Users\\Hunter Johnson\\Documents\\CSCI561\\project1DotFiles\\regex-test.dot"
    )
  )

(defun print-out-fa ()
  (fa-dot 
       (make-fa '((c 1 c)
               (c 0 d)
               (d 0 d)
               (d 1 c))
             'c
             '(d))
        "C:\\Users\\Hunter Johnson\\Documents\\CSCI561\\project1DotFiles\\trivial.dot"
       )
  )


;;;;;;;;;;;;;;;;;;;;;;
;;;; EXTRA CREDIT ;;;;
;;;;;;;;;;;;;;;;;;;;;;

;; ;; Return the complement of FA
;;All you need to do for this is flip the start and end states and then add edges for the e
;; explicit dead state.

;;;;;;;;;;;;;;;;;;;;;fa-complement code;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun fa-complement (fa)
  (setq fa
        (add-dead-state-edges fa))
  (setq fa 
        (flip-accept-and-non-accept fa))
  fa
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

(defun test-add-dead-state-edges-on-function-no-edges ()
  (format t "~%The dead state edges are~%")
  (princ (add-dead-state-edges (make-fa-no-edges)))
  )

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;TEST FUNCTIONS FOR COMPLIMENT;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun run-all-complement-tests (dot-file-path)
  (test-flip-accept-and-non-accept dot-file-path)
  (test-add-dead-states dot-file-path)
  (test-complement dot-file-path)
  (test-complement-three-state-1 dot-file-path)
  (test-complement-no-edges dot-file-path) 
  )

(defun test-flip-accept-and-non-accept (dot-file-path)
  (fa-dot
   (flip-accept-and-non-accept 
    (make-fa '((c 1 c)
               (c 0 d)
               (d 0 d)
               (d 1 c))
             'c
             '(d))
    )
   (concatenate 'string dot-file-path "flip_accept.dot")
   )
  )

(defun test-add-dead-states (dot-file-path)
  (fa-dot
   (add-dead-state-edges
    (make-fa '((q_0 a q_1)
               (q_1 b q_2)
               (q_1 a q_1)
               (q_2 b q_2))
             'q_0
             '(q_2))
    )
   (concatenate 'string dot-file-path "add_dead.dot")
   )
  )

(defun test-complement (dot-file-path)
  (fa-dot
   (fa-complement
    (make-fa '((q_0 a q_1)
               (q_1 b q_2)
               (q_1 a q_1)
               (q_2 b q_2))
             'q_0
             '(q_2))
    )
   (concatenate 'string dot-file-path "complement.dot")
   )
  )

(defun test-complement-three-state-1 (dot-file-path)
    (fa-dot
   (fa-complement
    (make-three-state-dfa-1)
    )
   (concatenate 'string dot-file-path "test-complement-three-state-1.dot")
   )
  )

(defun test-complement-no-edges (dot-file-path) 
  (fa-dot
   (fa-complement
    (make-fa-no-edges)
    )
   (concatenate 'string dot-file-path "test-complement-no-edges.dot")
   )
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;End of complement;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; *********************NOTE WE NEED TO PUT THE FA'S THROUGH NFA->DFA AND DFA MINIMIZE BEFORE EQUIVALENT WILL WORK*************
;; ;; Test whether two FA are equivalent

(defun fa-equivalent (fa-0 fa-1)
  (is-fa-empty (dfa-product fa-0 fa-1 #'xor))
  )


(defun xor (cond1 cond2)
  (or(equal cond1 (not cond2))(equal (not cond1) cond2))
  )

;; ;; Test whether FA-0 is subseteq of FA-1
 (defun fa-subseteq (fa-0 fa-1)
    (is-fa-empty (dfa-product fa-0 fa-1 #'a-not-b))
   )

(defun a-not-b (cond1 cond2)
  (equal cond1 (not cond2))
  )

(defun is-fa-empty (fa)
  (let* ((states-map (make-hash-table :test #'equal)))
    (init-hash-map-with-states states-map (finite-automaton-states fa))
    (bfs (finite-automaton-edges fa) states-map (finite-automaton-start fa))
    (evaluate-hash-map-and-accept states-map (finite-automaton-accept fa))
  )
)

(defun test-is-fa-empty ()
  (is-fa-empty
   (make-fa '((a 1 b)
              (b 1 c)
               (d 1 a))
            'a
             '(c))
   )
  )

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

(defun init-hash-map-with-states (hash-map list-of-states)
  (dolist (state list-of-states)
    (setf (gethash state hash-map) nil)
    )
  )
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Code for testing fa equilvance;;;;;


(defun test-two-state-equilances ()
  (format t "~%TEST CASES FOR EQUILVANCE")
  (format t "~%Not equilvant test case: ~%")
  (if (fa-equivalent
        (make-fa '((a 1 a)
                   (a 0 a)
                   (b 0 a)
                   (b 1 a))
                 'a
                 '(b))
        (make-fa '((c 1 c)
                   (c 0 c)
                   (d 0 c)
                   (d 1 c))
                 'c
                 '(c))
        
       )
      NIL
      (format t "PASS") 
    )
  
  (format t "~%Equilvant test case: ~%")
  (if (fa-equivalent
        (make-fa '((a 1 a)
                   (a 0 a)
                   (b 0 a)
                   (b 1 a))
                 'a
                 '(b))
        (make-fa '((c 1 c)
                   (c 0 c)
                   (d 0 c)
                   (d 1 c))
                 'c
                 '(d))
        
       )
      (format t "PASS") 
    NIL
    )
  
  )