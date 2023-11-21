# Exercises for Day 1

```rzk
#lang rzk-1
```

## Dependent types

**Exercise 1.1.** _(HoTT Book Exercise 1.1)_
Given functions `#!rzk f : A → B` and `#!rzk g : B → C`,
define their _composite_ `#!rzk compose A B C f g : A → C`.
Show that composition is associative (definitionally)
and unital (w.r.t. `#!rzk identity`).

```rzk
#define compose
  (A B C : U)
  (f : A → B) 
  (g : B → C)
  : A → C
  := \ a → g (f a)

#define compose-Association
 (A B C D : U)
 (f : A → B) 
 (g : B → C)
 (h : C → D)
 : compose A B D f (compose B C D g h)
   = compose A C D (compose A B C f g) h
 := refl
```

**Exercise 1.2.** _(HoTT Book Exercises 1.2 and 1.3)_
Derive recursion and induction principles for products `#!rzk rec-prod A B`
using only the projections `#!rzk pr₁` and `#!rzk pr₂`,
and verify that the definitional equalities are valid.
Do the same for Σ-types.

```rzk
#define rec-prod
  ( A B : U)
  ( C : U)
  ( f : A → B → C)
  : prod A B → C
  := (pr₁) -- ?
```


**Exercise 1.3.**
Show that Σ-types are associative in the following sense:

```rzk
#define reassoc-left-Σ
  ( A : U)
  ( B : A → U)
  ( C : (a : A) → B a → U)
  : (Σ (a : A), Σ (b : B a), C a b)
  → (Σ (ab : Σ (a : A), B a), C (pr₁ A B ab) (pr₂ A B ab))
  := _exercise

#define reassoc-right-Σ
  ( A : U)
  ( B : A → U)
  ( C : (a : A) → B a → U)
  : (Σ (ab : Σ (a : A), B a), C (pr₁ A B ab) (pr₂ A B ab))
  → (Σ (a : A), Σ (b : B a), C a b)
  := _exercise

#define assoc-left-Σ
  ( A : U)
  ( B : A → U)
  ( C : (a : A) → B a → U)
  ( abc : Σ (a : A), Σ (b : B a), C a b)
  : reassoc-right A B C (reassoc-left A B C abc) = abc
  := _exercise

#define assoc-right-Σ
  ( A : U)
  ( B : A → U)
  ( C : (a : A) → B a → U)
  ( abc : Σ (ab : Σ (a : A), B a), C (pr₁ A B ab) (pr₂ A B ab))
  : reassoc-left A B C (reassoc-left A B C abc) = abc
  := _exercise
```

## Propositions as types

**Exercise 1.3.** _(HoTT Book Exercise 1.11)_
Show that for any type `#!rzk A`, we have `#!rzk ¬ (¬ (¬ A)) → ¬ A`.

```rzk
#define triple-neg
  (A : U)
  : ¬ (¬ (¬ A))
  → (¬ A)
  := \ f a → f (\ b → b a)
```

**Exercise 1.4.** _(HoTT Book Exercises 1.12 and 1.13)_
Using propositions as types interpretation, prove the following tautologies:

1. If A, then (if B then A).
2. If A, then not (not A).
3. If (not A or not B), then not (A and B).
4. For any P, double negation of the law of excluded middle holds: not (not (not P or P)).

```rzk
--- 1.4.3
#define coprod-neg
  (A B : U)
  : coprod (¬ A) (¬ B)
  → ¬ ( prod A B)
  := \z -> \ (a, b) →
    rec-coprod (¬ A) (¬ B) Void 
    (\ na → na a)
    (\ nb → nb b)
    z

```
## Identity types

**Exercise 1.5.** _(HoTT Book Exercise 1.14)_
Why do the induction principles for identity types not allow us to construct a
the following function?

```{unchecked .rzk}
#define bad
  : (x : A)
  → (p : x = x)
  → p = refl_{x}
  := ind-path A x _ refl_{refl_{x}}
```

## Homotopy type theory

**Exercise 1.6.**
Formalize both proofs of HoTT Book Lemma 2.1.1.
Show that both proofs are equal.

**Exercise 1.7.**
Formalize both proofs of HoTT Book Lemma 2.1.2.
Show that both proofs are equal.

**Exercise 1.9.**
Formalize the proofs of HoTT Book Lemma 2.1.3.
Show that different proofs for each point in the lemma are equal.

### Loop space

Consider the definitions of loop space and 2-loop space (HoTT Book Definition 2.1.8):

```rzk
#define Ω
  ( A : U)
  ( a : A)
  : U
  := a =_{A} a

#define Ω²
  ( A : U)
  ( a : A)
  : U
  := Ω (Ω A a) refl_{a}

#define concat-Ω
  ( A : U)
  ( a : A)
  : Ω A a → Ω A a → Ω A a
  := concat A a a a
```

**Exercise 1.10.**
Formalize the proof of HoTT Book Theorem 2.1.6 (Eckmann-Hilton):

```rzk
#define Eckmann-Hilton
  ( A : U)
  ( a : A)
  ( α β : Ω A a)
  : concat-Ω A a α β = concat-Ω A a β α
  := _exercise
```
