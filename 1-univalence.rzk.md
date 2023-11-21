# Univalence

```rzk
#lang rzk-1

#define homotopy
  (A B : U)
  (f g : A → B)
  : U
  := (x : A) → f x = g x

#define is-equiv
  (A B : U)
  (f : A → B)
  : U
  := prod
      (Σ (r : B → A), homotopy A A (compose A B A f r) (identity A))
      (Σ (s : B → A), homotopy B B (compose B A B s f) (identity B))

#define Equiv
    (A B : U)
    : U
    := Σ (f : A → B), is-equiv A B f

#define UnivalenceAxiom
    : U
    := (A : U)
  → (B : U)
  → Equiv (A = B) (Equiv A B)

#postulate ua : UnivalenceAxiom

#define inv
    (A B : U)
    : Equiv A B → (B → A)
    := \ (f, ((r, er), (s, es))) → r

#define eq-from-Equiv
    (A B : U)
    : Equiv A B → (A = B)
    := inv (A = B) (Equiv A B)
            (ua A B)
```
