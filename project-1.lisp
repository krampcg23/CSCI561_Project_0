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
        (make-fa edges start (list accept))))))



(defun eps-closure(nfa unvisited start)
  (princ unvisited)
  ;(princ #\linefeed)
  (labels ((visit (c q)
             (princ c)
             (princ #\linefeed)
             (typecase c
               (symbol
                (if (equal q c)
                    c
                    (closure nfa q (list q c))
                    ))
               (list
                (if (member q c)
                    c
                    (closure nfa q (cons q c))
                    ))))
           (closure (nfa q newq)
             (let* ((edges (finite-automaton-edges nfa))
                    (p '()))
               (dolist (edge edges)
                 (if (equal q (car edge))
                     (if (equal :epsilon (cadr edge))
                         (cons p (car (cdr (cdr edge))))
                         )))
               (eps-closure nfa p newq)
               )))

    (let* ((c1 (reduce #'visit unvisisted :initial-value start)))
      c1)
    ))


(defun move-eps-closure(nfa q transition)
  (labels ((visit (c q)
             (let* ((p '())
                    (edges (finite-automaton-edges nfa)))
               (dolist (edge edges)
                 (if (equal q (car edge))
                     (if (equal transition (cadr edge))
                         (cons p (cdr (cdr edge)))
                         )))
               (eps-closure nfa p c))))
    (let* ((c1 (reduce #'visit (eps-closure nfa q '()) :initial-value '())))
      c1)
    )
  )

;; Convert a nondeterministic finite automaton to a deterministic
;; finite automaton
;;
(defun nfa->dfa (nfa)
  (let ((visited-hash (make-hash-table :test #'equal))
        (alphabet (remove :epsilon (finite-automaton-alphabet nfa))))
    (labels ((sort-state (u)
               (sort u #'state-predicate))
             (visit-state (edges subset) ; visit-state(e, u)
               (labels ((visit (edges subset) ; else case
                          (setf (gethash subset visited-hash) t)
                          (reduce #'visit-symbol alphabet :initial-value edges))
                        (visit-symbol (edges transition)
                          (let* ((u1 (move-eps-closure nfa subset transition)))
                            (if (not (equal u1 nil))
                                (visit-state (cons edges (list subset transition u1)) u1)
                                edges))))
                 (if (gethash subset visited-hash) ;subset already constructed
                     edges
                     (visit edges subset)))))
      (let* ((states (remove (finite-automaton-start nfa) (finite-automaton-states nfa)))
             (q01 (eps-closure nfa states (finite-automaton-start nfa)))
             (E1 (visit-state '() q01))
             (F1 '())
             (accepts (finite-automaton-accept nfa)))
        (dolist (accept accepts)
          (if (gethash accept visited-hash)
              (cons F1 accept)))
        (princ F1)
        (princ #\linefeed)
        (princ E1)
        (princ #\linefeed)
        (princ q01)
        (make-fa E1 q01 F1)))))
                             

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


;; Minimize the states in the dfa
(defun dfa-minimize (dfa)
  (TODO 'dfa-minimize))



;;;;;;;;;;;;;;;;;;;;;;
;;;; EXTRA CREDIT ;;;;
;;;;;;;;;;;;;;;;;;;;;;

;; ;; Return the complement of FA
;; (defun fa-complement (fa ))

;; ;; Test whether two FA are equivalent
;; (defun fa-equivalent (fa-0 fa-1))

;; ;; Test whether FA-0 is subseteq of FA-1
;; (defun fa-subseteq (fa-0 fa-1))
