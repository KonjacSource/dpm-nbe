#import "@preview/diatypst:0.9.3": *
#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#show: init-color-my-agda

#let nl-yellow = rgb("#F7D544")
#let nl-brown = rgb("#7A4A1E")
#let nl-cream = rgb("#FFF6D6")


#show: slides.with(
  title: "Implementation of Type Theory\n and Dependent Pattern Matching", // Required
  // date: "01.07.2024",
  authors: ("Qu Zhuoyuan . Nagoya University"),
  title-color: nl-yellow.darken(100%),
  theme: "full",
  count: none,
  toc: false,
)

#let nailoong-face(w) = {
  let h = w * 0.80
  let eye(cx) = {
    let ew = w * 0.20
    let eh = h * 0.25
    let cy = h * 0.47
    place(top + left, dx: w * cx - ew / 2, dy: cy - eh / 2,
      ellipse(width: ew, height: eh, fill: rgb("#CFE0A0")))
    place(top + left, dx: w * cx - w * 0.05, dy: cy - h * 0.04,
      ellipse(width: w * 0.1, height: h * 0.13, fill: black))
  }
  box(width: w, height: h, clip: true, {
    eye(0.27)
    eye(0.78)
    place(top + left, dx: w * 0.39, dy: h * 0.7,
      curve(
        stroke: 0.6pt + rgb("#8A5A1A"),
        curve.move((0pt, 0pt)),
        curve.line((w * 0.14, h * 0.045)),
        curve.line((w * 0.30, h * 0.005)),
      ))
  })
}

#set page(foreground: place(top + right, dx: -0.5cm, dy: 0.02cm, nailoong-face(0.95cm)))
// #set text(fill: nl-brown)
// #show strong: set text(fill: nl-yellow.darken(30%))
// #show emph: set text(fill: nl-yellow.darken(35%))
// #show footnote: set text(fill: nl-yellow.darken(30%))


#show raw.where(block: true): set text(size: 7pt)
#show raw.line: it => {
  show regex("\bCx\b|\bSb\b|\bTy\b|\bTm\b|\bI\b|\bℕ\b|\bℤ\b|\bType\b|\bProp\b|\bElim\b|\bMaybe\b|\bBool\b|\bValue\b|\bTern\b|\bContext\b"): set text(fill: purple)
  show regex("\bf\b|\bJust\b|\bNothing\b|\babs\b|\b0\b|\b1\b"): set text(fill: blue)
  show regex("\bopen\b"): set text(fill: green)
  show regex("\bdata\b|\bdef\b|\bfor\b|\bcase\b|\bof\b"): set text(fill: color.orange)
  show regex("\bap\b"): set text(fill: color.fuchsia)
  it
}

// Suggest

// + explain QIT
// + ap name is confusing
// + remove last two slides
// + too yellow

== Background

Type checking is an important topic in programming languages theory and type theory.

This talk introduces the basic ideas of dependent type checking and we talk about the implementation of dependent pattern matching.

== What is Type Checking?

#let Id = $bold("Id")$
#let UU = $cal("U")$
#let refl = $bold("refl")$
#let subst = $bold("subst")$
- For a type theory, let's say a basic MLTT with $Pi$-type, countable infinite universe $UU_n$, and $Id$.
We omit $Gamma tack$ on the left.

$
  (A : UU_i quad x : A tack B : UU_j)/
  (product_(x : A) B : UU_(max(i, j)))
$

#grid(columns: (3fr, 3fr), gutter: 1em)[
  $
    (x : A tack b : B)/
    (lambda x. b : product_(x : A) B)
  $][
  $
  (f : product_(x : A) B quad a : A)/
  (f(a) : B[a"/"x])
  $
]
#line(length:100%)
$
  (A : UU_i quad a : A quad b : A)/
  (Id_A (a, b) : UU_0)
$
#grid(columns: (3fr, 3fr), gutter: 1em)[
$
  refl_A (a) : Id_A (a, a)
$
][$
  (P : A → UU_i quad e : Id_A (a, b) quad p : P(a))/
  (subst_P (e, p) : P(b))
$]

== What is Type Checking? 

And we have conversion rules.

$
  (lambda x. b)(a) = b[a"/"x]
$

$
  subst_P (refl_A (a), p) = p
$

we omit $eta$-rules for now.

== What is Type Checking?
\

#let check = $bold("check")$
#let infer = $bold("infer")$
#let conv = $bold("conv")$
- Type checker is a decidable algorithm that given a term $t$ and a type $T$, and a context $Gamma$, decides whether $Gamma tack t : T$ holds or not.

  $
  check : (Γ : "Context") (t : "Term") (T : "Term") → "Bool"
  $

- Practically, we usually use so called bidirectional type checking, 
  
  $
  infer : (Γ : "Context") (t : "Term") → "Type" union.plus "Fail"
  $
  
- *Principle: check constructors, infer eliminators.*

and we also need a way to decide equality

$
  conv : (t : "Term") (u : "Term") → "Bool"
$

== How to Type Check?

First, we need a syntax.

```haskell
data Term 
  = U (n : Nat)
  | Var (x : Name)
  | Pi  (A B : Term)
  | Lam (x : Name) (b : Term)
  | App (f a : Term)
  | Id  (A a b : Term)
  | Refl (a : Term)
  | Subst (P e p : Term)

data Context 
  = []
  | (Γ : Context) , (x : Name) : (A : Term)
```

== How to Type Check?

Two ways to do conversion,

- *Substitution*

  Repeatly rewrite the term to normal form and compare the normal forms.

- *Normalization by Evaluation (NbE)*

  Use a semantic model (value) to evaluate the term and compare the semantic values.

  #grid(columns: (1fr, 1fr), gutter: 1em)[
  ```haskell
  data Value 
    = VU    (n : Nat)
    | VPi   (A : Value) 
            (B : Value → Value)
    | VLam  (f : Value → Value)
    | VId   (A a b : Value) 
    | VRefl (a : Value)
    | VNe   (n : Neutral)
  ```
  ][
  ```haskell
  data Neutral
    | NVar (x : Name)
    | NApp (f : NVar) (a : Value)
    | VSubst (P : Value) 
             (e : Neutral) 
             (p : Value)
  


  ```
  ]

== NbE

Neutral terms are values that stucked on a "head".

e.g.

$f(x)(y)(z)$ is a neutral term if $f$ is a variable.
we call $f$ the head and $x, y, z$ the spine.

$subst(P, e, p)$ is a neutral term if $e$ is a variable. we call $e$ the head and $P, p$ the spine.

== NbE


```haskell
data Env 
  = []
  | (g : Env) , (x : Name) ↦ (v : Value) 

eval : Env → Term → Value
eval g (U n)     = VU n
eval g (Var x)   = lookup g x
eval g (Pi A B)  = VPi (eval g A) (λ v → eval (g, x ↦ v) B)
eval g (Lam x b) = VLam (λ v → eval (g, x ↦ v) b)
eval g (App f a) = case eval g f of
  VLam f' → f' (eval g a)
  VNe n   → VNe (NApp n (eval g a))
eval g (subst P e p) = case eval g e of
  VRefl a → eval g p
  VNe n   → VNe (VSubst (eval g P) n (eval g p))
...
conv : Value → Value → Bool
conv (VU n)      (VU m)      = n == m
conv (VPi A1 B1) (VPi A2 B2) = conv A1 A2 && conv (B1 v) (B2 v) 
                               where v is a fresh-variable
...
```

== NbE

Handle $eta$-conversions.

```haskell
conv (VLam b)  f = conv (b v) (VApp f v) 
conv f  (VLam b) = conv (b v) (VApp f v) 
                 where v is a fresh-variable 
```

== NbE

NbE is faster than naive rewriting,

Consider the following example:

$
  (lambda x. f(x, x))" "t
$

$t$ is a very large term.

- Using NbE, we only evaluate $t$ once and keep it in the evaluation environment.

#align(center, diagram({
	node((0, -1), [$"eval" t$])
	node((-1, 1), [$f$])
	node((0, 1), [$x$])
	node((1, 1), [$x$])
	edge((0, 1), (0, -1), "->")
	edge((1, 1), (0, -1), "->")
}))

// When we use NbE, substitution disappears in our implementation.


== NbE

\
\
\

Since we almost generate a closure for each lambda, we can always use this trick to avoid substitution.

== Type Check 

```haskell
check : (Γ : Context) (t : Term) (T : Value) → Bool
check Γ (Lam x b) (Pi A B) = check (Γ, x : A) b (B x)
check Γ (Refl a) (Id A a b) = conv (eval Γ a) (eval Γ b)
check Γ t T = conv (infer Γ t) T

infer : (Γ : Context) (t : Term) → Value
infer Γ (Var x) = lookup Γ x
infer Γ (App f a) = case infer Γ f of
  VPi A B → B (eval Γ a)
  _       → error
...
```

== Type Check 

```haskell
check : (Γ : Context) (t : Term) (T : Value) → Bool
check Γ (Lam x b) (Pi A B) = check (Γ, x : A) b (B x)
check Γ (Refl a) (Id A a b) = conv (eval Γ a) (eval Γ b)
check Γ t T = conv (infer Γ t) T

infer : (Γ : Context) (t : Term) → Value
infer Γ (Var x) = lookup Γ x
infer Γ (App f a) = case infer Γ f of
  VPi A B → B (eval Γ a)
  _       → error
...
```

Type checking is decidable only if conversion is decidable. i.e. normalization.

== Type Check
\
\
\
Extensional equality is undecidable in general.
$
  (Gamma tack e : Id_A(a, b))/
  (Gamma tack a = b : A)
$
\
\
Lean is also undecidable, due to the presence of *proof irrelevant inductive propositions.*

== Dependent Pattern Matching

*Quick history of pattern matching*
- ?????. Mathematical Induction
- 1960s. HOPE programming language. 
- 1970s. Standard ML. (non-dependent type system)
- 1990s. Dependent pattern matching, introduced by Thierry Coquand.
- 2000s. DPM in non-dependent type system, a.k.a. GADTs.
- 2010s: 
  - HoTT.
  - Higher inductive types.
  - Pattern matching without K.
  - Pattern matching with boudaries.

== Dependent Pattern Matching
\
\
\
*Slogan: * when we have a new kind of inductive definition, we can always find a way to design a new syntax for pattern matching.

== Dependent Pattern Matching

- Indexed inductive types is a generalization of inductive types, where types can be indexed by terms or other types.

i.e. length-indexed list is an indexed inductive type

```haskell
data Vec (A : U) : Nat → U where
  nil      : Vec A 0
  cons {n} : (x : A) (xs : Vec A n) → Vec A (n + 1)
```

i.e. Martin-Löf's identity type is an indexed inductive type

```haskell
data Id (A : U) (x : A) : A → U where
  refl : Id A x x
```

== Dependent Pattern Matching

When we do pattern matching those types, we need to consider the indices.

```haskell
sym : Id A x y → Id A y x
sym refl = refl
```

How does it work? 

1. check the type of the pattern
  ```haskell
  refl : Id A x (x)   -- (index)
  ```
2. unify the index with the index of the given type (here is ``` Id A x (y)```)
  ```haskell
  x ~ y  =  [y/x] -- unification result is a substitution
  ```
3. apply the substitution to the RHS type.
  ```haskell
  (Id A y x) [y/x] = Id A y y
  ```

== Dependent Pattern Matching

Thus

```haskell
sym : Id A x y → Id A y x
sym refl = refl : Id A y y
```

== Dependent Pattern Matching

Unification has three possible results:
- *Success*: we can find a substitution that makes the two terms equal.
- *Positive Failure*: we can sure that there is no substitution that makes the two terms equal.
- *Negative Failure*: I don't know. i.e. $f(x) ~ f(y)$

$
  bold("solution")&: x ~ t &&= [t"/"x]\
  bold("injectivity")&: bold(c)(dash(t)) ~ bold(c)(dash(u)) &&= union.big_i t_i ~ u_i\
  bold("absurd")&: bold(c)(dash(t)) ~ bold(c')(dash(u)) &&= "Positive Failure"\
  ...
$
when we have a positive failure, we can safely say that such case is impossible and we can remove it from the pattern matching.
```haskell
head : Vec A (n + 1) → A
head (cons x xs) = x
```

== Dependent Pattern Matching Meets NbE

Unification gives us a substitution, and requires us to apply the substitution to the RHS type.

But we want to avoid substitution in NbE, because it breaks the sharing.

== Dependent Pattern Matching Meets NbE

A solution is to use a *delayed substitution*, which is a substitution that is not applied immediately, but is stored in the evaluation environment and applied when needed. 

This solution is proposed by András Kovács.

== Dependent Pattern Matching Meets NbE

```haskell
data Value 
  = ... 
  | VSub (v : Value) (σ : Sub) 

data Neutral 
  = ... 
  | NSub (v : Neutral) (σ : Sub)

force : Value → Value
force (VSub v σ) = force (applySub v σ)
force v = v

forceN : Neutral → Value 
forceN (NSub n σ) = app (applySub h σ) (applySub sp σ)
                  where h  = head of n
                        sp = spine of n
forceN n = VNe n

app (VLam f) v = f v
app (VNe n) v = VNe (NApp n v)
...
```

== Dependent Pattern Matching Meets NbE

This solution is not perfect 

$(f" "x" "x )[t"/"x]  = f (x[t"/"x])" "(x[t"/"x])$ 

== Dependent Pattern Matching Meets NbE

A better solution is to use *glued evaluation*, 

```haskell
data Value 
  = ... 
  | VSub (v : Value) (σ : Sub) (~ result : Value)
```

when we construct a ```hs VSub```, the ```hs result``` field is lazy.

#align(center, diagram({
	node((0, -1), [```hs VSub x [t/x] (~t)```])
	node((-1, 1), [$f$])
	node((0, 1), [$x [t"/"x]$])
	node((1, 1), [$x [t"/"x]$])
	edge((0, 1), (0, -1), "->")
	edge((1, 1), (0, -1), "->")
}))

== Dependent Pattern Matching Meets NbE

 But to my experience, the original solution is good enough for dependent pattern matching.



Nope. glued is wayyyyyyyyyyy faster.