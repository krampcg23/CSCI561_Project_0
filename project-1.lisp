;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; STARTER DEFINITIONS FOR FINITE AUTOMATA ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Fold-left from project 0
;; Examples:
;;   (fold-left #'- 1 '(2 3)) => -4
(defun fold-left (function initial-value list)
  (cond
    ((not list) initial-value)
    (t (fold-left function (funcall function initial-value (car list)) (cdr list)))))


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

(defun TODO (thing)
  (error "Unimplemented: ~A" thing))

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
        (format t "~% The edges are:  ~%")
        (princ edges)
        (format t "~% The accepts are ~%")
        (princ (list accept))
        (make-fa edges start (list accept))))))



;; Convert a nondeterministic finite automaton to a deterministic
;; finite automaton
;;
(defun nfa->dfa (nfa)
  (let ((visited-hash (make-hash-table :test #'equal))
        (alphabet (remove :epsilon (finite-automaton-alphabet nfa))))
    (labels ((sort-state (u)
               (sort u #'state-predicate))
             (visit0 (edges subset)
               (if (gethash subset visited-hash)
                   edges
                   (visit edges subset)))
             (visit (edges subset)
               (setf (gethash subset visited-hash) t)
               (TODO 'nfa->dfa-visit))))
    (TODO 'nfa->dfa)))

;; Compute the intersection between the arguments
(defun dfa-intersection (dfa-0 dfa-1)
  (let ((states (make-hash-table :test #'equal))
        (edges))
    (labels ((visit (q)
               (unless (gethash q states)
                 (setf (gethash q states) t)
                 (destructuring-bind (q0 q1) q
                   (TODO 'dfa-intersection)))))
      (let ((s (list (finite-automaton-start dfa-0)
                     (finite-automaton-start dfa-1))))
        (visit s)
        (TODO 'dfa-intersection)))))


;;This is my implementation of intersection.  I am not sure if this is different from what he wants????
(defun dfa-intersection-hunter-version (dfa-0 dfa-1)
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
              (if (equal
                   (equal (cadr dfa-0-edge) (finite-automaton-start dfa-0))
                   (equal (cadr dfa-1-edge) (finite-automaton-start dfa-1)))
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
    (format t "End of dfa-product")
    (make-fa product-dfa-edges start-state end-states)
    )
  )

;; Minimize the states in the dfa
(defun dfa-minimize (dfa)
  (TODO 'dfa-minimize))
(defun test-dfa-product () 
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
   "C:\\Users\\Hunter Johnson\\Documents\\CSCI561\\project1DotFiles\\test_product_dfa.dot"
   )
  )
;;This is the example from the slide
(defun test-dfa-intersection ()
  (fa-dot
   (dfa-intersection-hunter-version 
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
   "C:\\Users\\Hunter Johnson\\Documents\\CSCI561\\project1DotFiles\\test-intersection-dfa.dot"
   )
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
;; (defun fa-complement (fa ))

;; ;; Test whether two FA are equivalent
;; (defun fa-equivalent (fa-0 fa-1))

;; ;; Test whether FA-0 is subseteq of FA-1
;; (defun fa-subseteq (fa-0 fa-1))
