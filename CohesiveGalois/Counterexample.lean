import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

-- #check DualNumber.eps
-- #print TrivSqZeroExt
-- #synth CommRing (TrivSqZeroExt ℤ ℤ)
-- #print DualNumber.eps


abbrev R := DualNumber ℤ

theorem square_neq_one_plus_eps (x : R) : x ^ 2 ≠ 1 + DualNumber.eps := by
  by_contra h_contra
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, x = TrivSqZeroExt.inl a + TrivSqZeroExt.inr b := by
    aesop;
  simp_all +decide [ sq, TrivSqZeroExt.ext_iff ];
  have ha : a = 1 ∨ a = -1 := by
    exact Int.eq_one_or_neg_one_of_mul_eq_one h_contra.1;
  rcases ha with ( rfl | rfl ) <;> linarith [ show b = 0 by linarith ]

/-
Define S as R[δ] / (δ^2 - (1+ε)).
-/
noncomputable def S := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (1 + DualNumber.eps : R))
open CommRing Ideal CommRing
instance : CommRing S := Ideal.Quotient.commRing _
instance : Algebra R S := Ideal.Quotient.algebra R

inductive C_Obj where
| Base
| Cover
deriving DecidableEq, Repr

noncomputable def C_Obj.toRing : C_Obj → Type
| .Base => R
| .Cover => S

noncomputable instance (t : C_Obj) : CommRing (t.toRing) :=
  match t with
  | .Base => by
    simp [C_Obj.toRing]
    exact inferInstance
  | .Cover => by
    simp [C_Obj.toRing]
    exact inferInstance

noncomputable instance (t : C_Obj) : Algebra R (t.toRing) :=
  match t with
  | .Base => Algebra.id R
  | .Cover => by
    simp [C_Obj.toRing]
    exact inferInstance


def Real_Hom (A B : C_Obj) := B.toRing →ₐ[R] A.toRing

instance : CategoryTheory.Category C_Obj where
  Hom := Real_Hom
  id X := AlgHom.id R (X.toRing)
  comp f g := AlgHom.comp f g -- Contravariant!!!

noncomputable def p_alg : Real_Hom .Cover .Base := Algebra.ofId R S


theorem hom_base_to_cover_empty : IsEmpty (Real_Hom .Base .Cover) := by
  rw [Real_Hom]
  dsimp [C_Obj.toRing]
  refine ⟨fun f => ?_⟩

  let eps_R : R := 1 + DualNumber.eps
  let P : Polynomial R := Polynomial.X ^ 2 - Polynomial.C eps_R
  let root_S : S := AdjoinRoot.root P

  have h_S_identity : root_S ^ 2 = algebraMap R S eps_R := by
    have h_eval := AdjoinRoot.eval₂_root P
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C] at h_eval
    exact eq_of_sub_eq_zero h_eval


  let y := f root_S
  have h_R_identity : y ^ 2 = eps_R := by
    apply_fun f at h_S_identity
    rw [map_pow] at h_S_identity
    rw [AlgHom.commutes] at h_S_identity
    exact h_S_identity
  exact square_neq_one_plus_eps y h_R_identity

open CategoryTheory

def Shape : C_Obj ⥤ Type 0 := (CategoryTheory.Functor.const C_Obj).obj PUnit

theorem projection_not_iso : ¬ CategoryTheory.IsIso (C := C_Obj) p_alg := by
  intro h_iso
  let inv := @CategoryTheory.inv C_Obj _ _ _ p_alg h_iso
  exact hom_base_to_cover_empty.false inv




-- ====== MAIN RESULT ======


theorem shape_not_conservative : ¬ CategoryTheory.Functor.ReflectsIsomorphisms Shape := by
  intro h_reflects
  let f : C_Obj.Cover ⟶ C_Obj.Base := p_alg

  have h_pi_iso : CategoryTheory.IsIso (C := Type 0) (Shape.map f) := by
    dsimp [Shape]
    infer_instance

  have h_f_iso : CategoryTheory.IsIso f :=
    h_reflects.reflects f

  exact projection_not_iso h_f_iso
