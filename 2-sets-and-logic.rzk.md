```rzk
#lang rzk-1

#variables A B : U


#define is-set
    (A : U)
    : U
    := (x : A)
    → (y : A)
    → (p : x = y)
    → (q : x = y)
    → (p = q)

#define is-set-Unit
    : is-set Unit
    := \unit unit ( p : unit = unit) (q : unit = unit) →
        ind-path Unit unit
            (\ unit  s → s = q)
            (ind-path Unit unit
                ( \ unit s' → refl_{unit} = s' ) --C
                refl
                unit
                q)
            unit
            p


#define is-set-Void
    : is-set Void
    := \ x _ p q → ind-Void(\ z  → p = q ) x
        
#define eq-pr1
    (A B : U)
    (x a : A)
    (y b : B)
    : ((x, y) =_{prod A B} (a, b)) → (x =_{A} a)
    := ind-path (prod A B) (x, y)
        (\ (w1, w2) _ → x = w1) --C
        refl_{x} --base case
        (a, b)

#define eq-pr2
    (A B : U)
    (x a : A)
    (y b : B)
    : ((x, y) =_{prod A B} (a, b)) → (y =_{B} b)
    := ind-path (prod A B) (x, y)
        (\ (w1, w2) _ → y  = w2) --C
        refl_{y} --base case
        (a, b)

#define eq-prod
    (x a : A)
    (y b : B)
    ((p, q) : prod (x = a) (y = b))
    : (x, y) =_{prod A B} (a, b)
    := ind-path A x
          (\ w1 _ → (x, y) =_{prod A B} (w1, b)) -- C
        (ind-path B y
            (\ w2 _ → (x, y) = (x, w2)) -- C
            -- base case: (x, y) = (x, y)
            refl_{(x, y)}
            b q)
        a p


-- #define compose
--     (A B C : U)
--     (f : A → B)
--     (g : B → C)
--     : A → C
--     := \ x → g (f x)


#define eq-pr₁
  (x a : A)
  (y b : B)
  : ((x, y) =_{prod A B} (a, b)) → (x =_{A} a)
  := ind-path (prod A B) (x, y)
      (\ (w1, w2) _ → x = w1 ) -- C
      refl_{x} -- base case
      (a, b)

#define eq-pr₂
  (x a : A)
  (y b : B)
  : ((x, y) =_{prod A B} (a, b)) → (y =_{B} b)
  := ind-path (prod A B) (x, y)
      (\ (w1, w2) _ → y = w2 ) -- C
      refl_{y} -- base case
      (a, b)

#define eq-prod-inv
  (x a : A)
  (y b : B)
  (p : (x, y) =_{prod A B} (a, b))
  : prod (x = a) (y = b)
  := (eq-pr₁ x a y b p , eq-pr₂ x a y b p)

#define is-retract-eq-prod
  (x a : A)
  (y b : B)
  (p : (x, y) =_{prod A B} (a, b))
  : eq-prod x a y b (eq-prod-inv x a y b p) = p
  := ind-path (prod A B) (x, y)
      (\ (w1, w2) s →
          eq-prod x w1 y w2
            (eq-prod-inv x w1 y w2 s)
            = s ) -- C
      refl -- base case   eq-prod (eq-prod-inv refl_{(x, y)}) = refl_{(x, y)}
      (a, b) p


#define is-section-eq-prod
  (x a : A)
  (y b : B)
  ((p, q) : prod (x = a) (y = b))
  : eq-prod-inv x a y b (eq-prod x a y b (p, q)) = (p, q)
  := ind-path A x
       (\ w1 s1 →
            eq-prod-inv x w1 y b
              (eq-prod x w1 y b (s1, q))
              = (s1, q)) -- C
       (ind-path B y
        (\ w2 s2 →
            eq-prod-inv x x y w2
              (eq-prod x x y w2 (refl, s2))
              = (refl, s2)) -- C'
        refl
        b q)
        a p


#define is-equiv-eq-prod
  (x a : A)
  (y b : B)
  : is-equiv
        (prod (x = a) (y = b))
        ((x, y) =_{prod A B} (a, b))
        (eq-prod x a y b)
  := ((eq-prod-inv x a y b , is-section-eq-prod x a y b),
    (eq-prod-inv x a y b , is-retract-eq-prod x a y b))

#define eq-func
    (x a : A)
    (y b : B)
    : is-equiv
        (eq-pr₁ x y ) (eq-pr₁ q)
        (eq-pr₂ p) (eq-pr₂ q)