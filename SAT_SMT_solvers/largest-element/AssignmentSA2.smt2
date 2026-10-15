; Assignment SA-2: largest element in an array
; Francisco José Sánchez de León Acevedo
; Each assertion negates a VC from the shown in the pdf, then unsat proves that VC valid

(declare-const v (Array Int Int))
(declare-fun len ((Array Int Int)) Int)
(declare-const i Int)
(declare-const m Int)
(declare-const k Int)

; VC1: Invariant holds at the beginning of the loop
(push)
(assert
  (not
    (=>
      (and
        (>= (len v) 1)
        (= i 1)
        (= m 0))
      ; Left hand side (before loop) implies the invariant
      (and
        (<= 0 i)
        (<= i (len v))
        (<= 0 m)
        (< m (len v))
        (forall ((j Int))
          (=>
            (and (<= 0 j) (< j i))
            (>= (select v m) (select v j))))))))
(check-sat)
(pop)

; VC2: Invariant holds after each iteration
(push)
(assert
  (not
    (=>
      (and
        ; invariant
        (<= 0 i)
        (<= i (len v))
        (<= 0 m)
        (< m (len v))
        (forall ((j Int))
          (=>
            (and (<= 0 j) (< j i))
            (>= (select v m) (select v j))))
        ; b (while condition)
        (< i (len v)))
      (and
        ; Both array accesses are within bounds
        (<= 0 i)
        (< i (len v))
        (<= 0 m)
        (< m (len v))

        ; if first branch: m = i and i = i + 1
        (=>
          (> (select v i) (select v m))
          (and
            (<= 0 (+ i 1))
            (<= (+ i 1) (len v))
            (<= 0 i)
            (< i (len v))
            (forall ((j Int))
              (=>
                (and (<= 0 j) (< j (+ i 1)))
                (>= (select v i) (select v j))))))

        ; Else branch: skip and i := i + 1
        (=>
          (<= (select v i) (select v m))
          (and
            (<= 0 (+ i 1))
            (<= (+ i 1) (len v))
            (<= 0 m)
            (< m (len v))
            (forall ((j Int))
              (=>
                (and (<= 0 j) (< j (+ i 1)))
                (>= (select v m) (select v j))))))))))
(check-sat)
(pop)

; VC3: Postcondition holds after each iteration
(push)
(assert
  (not
    (=>
      (and
        ; Invariant
        (<= 0 i)
        (<= i (len v))
        (<= 0 m)
        (< m (len v))
        (forall ((j Int))
          (=>
            (and (<= 0 j) (< j i))
            (>= (select v m) (select v j))))
        ; Negated b (while condition) equal to (>= i (len v))
        (not (< i (len v))))
      (and
        ; Postcondition 
        (<= 0 m)
        (< m (len v))
        (forall ((j Int))
          (=>
            (and (<= 0 j) (< j (len v)))
            (>= (select v m) (select v j))))))))
(check-sat)
(pop)

; VC4: Termination measure is non-negative
(push)
(assert
  (not
    (=>
      (and
        ; Invariant
        (<= 0 i)
        (<= i (len v))
        (<= 0 m)
        (< m (len v))
        (forall ((j Int))
          (=>
            (and (<= 0 j) (< j i))
            (>= (select v m) (select v j)))))
      ; Implies that the termination measure is, at the end, greater or equal to 0
      (>= (- (len v) i) 0))))
(check-sat)
(pop)

; VC5: Termination measure decreases after each iteration
(push)
(assert
  (not
    (=>
      (and
        ; Invariant 
        (<= 0 i)
        (<= i (len v))
        (<= 0 m)
        (< m (len v))
        (forall ((j Int))
          (=>
            (and (<= 0 j) (< j i))
            (>= (select v m) (select v j))))
        ; b or while condition
        (< i (len v))
        ; Termination measure after the iteration equals k
        (= (- (len v) i) k))
      ; K decreases compared to last iteration
      (< (- (len v) (+ i 1)) k))))
(check-sat)
(pop)