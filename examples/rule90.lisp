(defmacro and (a b)
  (list 'cond (list a b)))

(defun rule (l m r)
  (cond ((and (and (eq l 1) (eq m 1)) (eq r 1)) 0)
        ((and (and (eq l 1) (eq m 0)) (eq r 1)) 0)
        ((and (and (eq l 0) (eq m 1)) (eq r 0)) 0)
        ((and (and (eq l 0) (eq m 0)) (eq r 0)) 0)
        (t 1)))

(defun next-cells (l m cells)
  (cond ((eq cells nil)
         (cons
          (rule l m 0)
          (list (rule m 0 0))))
        (t
         (cons
          (rule l m (car cells))
          (next-cells m (car cells) (cdr cells))))))

(defun print-space (n)
  (cond ((eq n 0) nil)
        (t (prin1 '_)
           (print-space (- n 1)))))

(defun print-cells (cells)
  (cond ((eq cells nil) nil)
        (t (prin1
            (cond ((eq (car cells) 0) '_)
                  (t 'A)))
           (print-cells (cdr cells)))))

(defun print-line (cells n)
  (print-space n)
  (print-cells cells)
  (print-space n)
  (terpri))

(defun rule90 (n cells)
  (cond ((eq cells nil) (rule90 n (list 1)))
        ((> n 0) (print-line cells n)
         (rule90
          (- n 1)
          (next-cells 0 0 cells)))))

(rule90 50 nil)
