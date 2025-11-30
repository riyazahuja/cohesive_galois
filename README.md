# Cohesion-Sensitive Galois Theory in Cohesive $\infty$-Topoi: A formalization

Alongside our work in ["Cohesion-Sensitive Galois Theory in Cohesive $\infty$-Topoi"](writeup.pdf), we aim to formalize the core arguments of the paper in Lean 4. Namely, we currently isolate a simplification of an algebraic counterexample to the conservativism of the shape functor on cohesive $\infty$-topoi. We hope to develop this formalization further to better encompass and describe the full work.

At the level of cohesive $\infty$-topoi, we study a counterexample showing that the shape functor can fail to be conservative on finite locally constant objects because of purely infinitesimal finite covers (non-trivial $\mu_2$–torsors over nilpotent thickenings that trivialize under shape). In lean, we study the minimal algebraic situation where this phenomenon appears and prove that a “shape-like” functor does not reflect isomorphisms.


## Algebraic Setup: Dual Numbers and an Exotic Square Root

We work over the ring of dual numbers
$R := \mathbb{Z}[\varepsilon]/(\varepsilon^2) \;\cong\; \texttt{DualNumber ℤ}$,
implemented in [Mathlib](https://github.com/leanprover-community/mathlib4) as `DualNumber ℤ`. Dual numbers are of the form $a + b\varepsilon$ with $\varepsilon^2 = 0$ and appear both in algebra and in synthetic differential geometry as the first-order infinitesimal thickening of a point.

In the infinitesimal counterexample in the paper, the key object is a non-trivial $\mu_2$–torsor over a nilpotent thickening, obtained by adjoining a square root of $1+\varepsilon$. Algebraically, we want to show:

**There is no element $x \in R$ such that $x^2 = 1 + \varepsilon$.**

In Lean:

```lean
abbrev R := DualNumber ℤ

theorem square_neq_one_plus_eps (x : R) : x ^ 2 ≠ 1 + DualNumber.eps := by
  by_contra h_contra
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, x = TrivSqZeroExt.inl a + TrivSqZeroExt.inr b := by
    aesop
  simp_all +decide [sq, TrivSqZeroExt.ext_iff]
  have ha : a = 1 ∨ a = -1 := by
    exact Int.eq_one_or_neg_one_of_mul_eq_one h_contra.1
  rcases ha with (rfl | rfl) <;> linarith [show b = 0 by linarith]
```

The proof proceed as follows:
1. Any $x \in R$ can be written uniquely as $x = a + b\varepsilon$ with $a,b \in \mathbb{Z}$. In mathlib this is TrivSqZeroExt.inl a + TrivSqZeroExt.inr b. ￼
2.	The equation $x^2 = 1 + \varepsilon$ translates to:
(a^2) + (2ab)\varepsilon \;=\; 1 + \varepsilon.
So we must have
a^2 = 1,\quad 2ab = 1.
3.	From $a^2=1$ over $\mathbb{Z}$, we get $a = \pm 1$ (Int.eq_one_or_neg_one_of_mul_eq_one).
4.	In either case, $2ab$ is even, so it cannot equal $1$. Contradiction.

So there is no solution to $x^2 = 1 + \varepsilon$ in $R$.

This is exactly the computation used in the paper to argue that the $\mu_2$–torsor given by $\delta^2 = 1+\varepsilon$ is non-trivial: if the torsor were trivial, there would be a global choice of square root, contradicting this lemma.



## Adjoining a Formal Root: The Extension Ring S

We now formally adjoin a square root of $1+\varepsilon$ to $R$. Using Mathlib’s `AdjoinRoot`, we define
$S := R[\delta] / \big(\delta^2 - (1 + \varepsilon)\big)$,
i.e. the quotient of $R[X]$ by the polynomial $X^2 - (1 + \varepsilon)$. ￼

In Lean:
```lean
noncomputable def S :=
  AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (1 + DualNumber.eps : R))

instance : CommRing S := Ideal.Quotient.commRing _
instance : Algebra R S := Ideal.Quotient.algebra R
```
By construction, the distinguished element `AdjoinRoot.root P (where P = X^2 - (1+ε))` satisfies $\texttt{root}^2 = 1+\varepsilon \in S$,
simply because that’s the defining relation of the quotient ring. This is captured by the Mathlib lemma `AdjoinRoot.eval₂_root`, and we package it as:
```lean
  [...]
  let eps_R : R := 1 + DualNumber.eps
  let P : Polynomial R := Polynomial.X ^ 2 - Polynomial.C eps_R
  let root_S : S := AdjoinRoot.root P

  have h_S_identity : root_S ^ 2 = algebraMap R S eps_R := by
    have h_eval := AdjoinRoot.eval₂_root P
    [...]
```
So $S$ is exactly the infinitesimal extension used in the paper’s Failure of $F5$ section: a nilpotent thickening with an adjoined square root of $1+\varepsilon$. The corresponding $\mu_2$–torsor is the data of this square root.



## Two Objects and Contravariant Algebra Maps

We package $R$ and $S$ into a tiny category C_Obj with just two objects:

```lean
inductive C_Obj where
| Base
| Cover
deriving DecidableEq, Repr

noncomputable def C_Obj.toRing : C_Obj → Type
| .Base  => R
| .Cover => S
```

Each object is interpreted as an $R$–algebra:
```lean
noncomputable instance (t : C_Obj) : CommRing (t.toRing) := [...]
noncomputable instance (t : C_Obj) : Algebra R (t.toRing) := [...]
```
Morphisms are $R$–algebra homomorphisms, but contravariant in the intended geometric sense:
```lean
def Real_Hom (A B : C_Obj) := B.toRing →ₐ[R] A.toRing
```
So a morphism Real_Hom A B is an $R$–algebra map $B \to A$, which we read as the geometric map $\textsf{Spec}(A) \longrightarrow \textsf{Spec}(B)$.

We turn this into a Lean Category:
```lean
instance : CategoryTheory.Category C_Obj where
  Hom X Y := Real_Hom X Y
  id X    := AlgHom.id R (X.toRing)
  comp f g := AlgHom.comp f g
```
The basic “covering projection” in this toy category is the algebra map
$R \to S$,
seen as a morphism Cover ⟶ Base (remember the contravariance). In Lean:
```lean
noncomputable def p_alg : Real_Hom .Cover .Base := Algebra.ofId R S
```
So:
- Base corresponds to the infinitesimal point $\textsf{Spec}(R)$,
- Cover corresponds to $\textsf{Spec}(S)$,
- `p_alg` : Cover ⟶ Base is the “infinitesimal $\mu_2$–cover” (the torsor).

This is the algebraic fragment of the “purely infinitesimal cover” that violates axiom $F5$.


## No $R$-Algebra Map $S \to R$

Next we show that there is no $R$–algebra homomorphism $S \to R$, i.e. no morphism Base ⟶ Cover in `C_Obj`. This is a simplification of the idea that the torsor is nontrivial and has no global section over the infinitesimal base.

In Lean:

```lean
theorem hom_base_to_cover_empty : IsEmpty (Real_Hom .Base .Cover) := by
  rw [Real_Hom]
  dsimp [C_Obj.toRing]
  refine ⟨fun f => ?_⟩

  let eps_R : R := 1 + DualNumber.eps
  let P : Polynomial R := Polynomial.X ^ 2 - Polynomial.C eps_R
  let root_S : S := AdjoinRoot.root P

  have h_S_identity : root_S ^ 2 = algebraMap R S eps_R := by
    [...]
  let y := f root_S
  have h_R_identity : y ^ 2 = eps_R := by
    apply_fun f at h_S_identity
    rw [map_pow] at h_S_identity
    rw [AlgHom.commutes] at h_S_identity
    exact h_S_identity

  exact square_neq_one_plus_eps y h_R_identity
```

Conceptually:
1. Assume $f : S \to R$ is an $R$–algebra hom.
2. In $S$, the distinguished element $\delta := $`root_S` satisfies $\delta^2 = 1+\varepsilon$.
3.	Apply $f$:
$f(\delta)^2 = f(1+\varepsilon) = 1+\varepsilon \in R$,
since $f$ is $R$–linear and fixes elements of $R$.
4.	This contradicts square_neq_one_plus_eps. So such $f$ cannot exist.

Thus:
```lean
theorem projection_not_iso : ¬ CategoryTheory.IsIso (C := C_Obj) p_alg := by
  intro h_iso
  let inv := @CategoryTheory.inv C_Obj _ _ _ p_alg h_iso
  exact hom_base_to_cover_empty.false inv
```
i.e. `p_alg` is not an isomorphism in `C_Obj`.

Geometrically: the infinitesimal $\mu_2$–cover has no inverse; it is a genuinely nontrivial finite cover over the infinitesimal base.


## The Shape(-Like) Functor That Forgets Infinitesimals

Now we build a “shape” functor

$\texttt{Shape} : \verb|C_Obj| \to \mathsf{Type}$

deliberately chosen to forget all infinitesimal data:

```lean
def Shape : C_Obj ⥤ Type 0 := (CategoryTheory.Functor.const C_Obj).obj PUnit
```
So:
- `Shape.obj Base = PUnit`,
- `Shape.obj Cover = PUnit`,
- and every morphism is mapped to the identity `PUnit → PUnit`.

In particular, for any morphism $f$, `Shape.map f` is an isomorphism in `Type 0` (it’s literally `id`!). For our cover:
```lean
have h_pi_iso : CategoryTheory.IsIso (C := Type 0) (Shape.map f) := by
  dsimp [Shape]
  infer_instance
```
This is a simplified version of the true shape functor in a cohesive $\infty$-topos: it forgets infinitesimal structure and remembers only the underlying homotopy type (here, both objects have the same “shape”, a singleton). ￼



## Shape Is Not Conservative: The Lean Theorem

Finally, we show that this shape-like functor does not reflect isomorphisms:
```lean
theorem shape_not_conservative :
  ¬ CategoryTheory.Functor.ReflectsIsomorphisms Shape := by
  intro h_reflects
  let f : C_Obj.Cover ⟶ C_Obj.Base := p_alg

  have h_pi_iso : CategoryTheory.IsIso (C := Type 0) (Shape.map f) := by
    dsimp [Shape]
    infer_instance

  -- If Shape reflects isos, then f must be an iso:
  have h_f_iso : CategoryTheory.IsIso f :=
    h_reflects.reflects f

  -- But we already proved p_alg is not an iso:
  exact projection_not_iso h_f_iso
```
In english:
- `Shape.map p_alg` is an isomorphism (because it’s the identity on PUnit),
- but `p_alg` itself is not an isomorphism,
- hence `Shape` cannot reflect isomorphisms.

This is the miniature version of the global statement: shape is not conservative on finite locally constant objects when purely infinitesimal covers exist.

## Cohesive $\infty$-Topoi and Axiom F5

Going back to the full generality, in the paper, the infinitesimal counterexample uses a point with a Weil algebra
$A = \mathbb{Z}[\varepsilon]/(\varepsilon^2)$

interpreting $\textsf{Spec}(A)$ as a first-order infinitesimal neighborhood. This is exactly `R := DualNumber ℤ` in Lean. ￼

Moreover, the extension

$T := \textsf{Spec}\big(\mathbb{Z}[\varepsilon,\delta] / (\varepsilon^2, \delta^2 - (1+\varepsilon))\big)$

gives a $\mu_2$–torsor over $\textsf{Spec}(A)$ that is nontrivial but has trivial shape. In the Lean model, `S` is the ring in which $\delta$ lives; the nontriviality is exactly the lemma `hom_base_to_cover_empty`.

Axiom $F5$ says that there are no covering families supported purely on nilpotent thickenings. When $F5$ fails, you can have finite covers that are invisible to shape, i.e. trivial after applying $\textsf{Shape}$ but nontrivial in the cohesive topos. This is the mechanism behind the failure of faithfulness of $\textsf{Shape}_* : \textsf{LCfin}(\mathcal{E}) \to \textsf{LCfin}(\mathcal{S}^\infty)$ in the global argument.

In the Lean model:
- The category `C_Obj` is a tiny 1-categorical skeleton of the infinitesimal part of the site. It only has two objects (the base infinitesimal point and its infinitesimal cover) and algebra maps between them.
- The functor `Shape` is the restriction of the global shape functor to this little subcategory: it remembers only the underlying homotopy type (which is just a point in both cases) and forgets infinitesimal data.
- The morphism `p_alg` : Cover ⟶ Base is a nontrivial finite cover in `C_Obj`, but `Shape.map p_alg` is an isomorphism. This is identical to the pattern of a “nontrivial finite cover that becomes trivial under shape” described in the paper’s Section on Failure of $F5$.

And the theorem
```lean
theorem shape_not_conservative :
  ¬ CategoryTheory.Functor.ReflectsIsomorphisms Shape
```
models, in this $1$-categorical algebraic fragment, the failure of shape to be conservative (or faithful on morphisms) on finite locally constant objects once you allow purely infinitesimal covers.



## Future Development

Our immediate next steps are currently to:
- Enrich `C_Obj` to a small site (a category with a coverage) and consider sheaves over it, recovering a toy cohesive topos.
- Define a finite Galois category of finite locally constant objects in this toy topos and compare it to the finite Galois category after applying a shape-like truncation.
- Show that the failure of `ReflectsIsomorphisms` at the level of raw algebra already implies failure of faithfulness/essential surjectivity at the level of finite covers.