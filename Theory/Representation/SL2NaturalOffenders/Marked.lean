module
public import Theory.Representation.SL2NaturalOffenders.Internal
public import Mathlib.LinearAlgebra.Quotient.Card
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Sylow detection with marked natural coordinates

For an action identified with the natural plane of the actual matrix group
SL₂(F), a nontrivial actor fixes at most one field line. A two-subgroup has
order at most |F|. Consequently its fixed-quotient order is at least its
order; the reverse inequality forces the actor to be Sylow of order |F|.
Both the actor isomorphism and the vector coordinates stay explicit.

This is the natural-module counting step used after DGS, *Groups and Graphs*
(1985), (5.12), in (7.1), printed pp.126–127. It does not recognize an
arbitrary rank-one action as natural.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.SL2NaturalOffenders
variable {D F W : Type*} [Group D] [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W]

omit [CharP F 2] in
/-- A nontrivial actor on the marked natural plane has fixed index at least
its defining field order. -/
theorem marked_field_card_le_fixed_quotient
    (e : D ≃* SL(2,F)) (σ : Representation (ZMod 2) D W)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (hE : ∀ g w, E (σ g w) = Matrix.mulVec (e g).val (E w))
    {A : Subgroup D} (hne : A ≠ ⊥) :
    Nat.card F ≤ Nat.card (W ⧸ fixedSpace σ A) := by
  let : Finite W := Finite.of_equiv (Fin 2 → F) E.toEquiv.symm
  obtain ⟨⟨a,ha⟩,hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hmat : (e a).val ≠ 1 := by
    intro h
    exact hne (Subtype.ext (e.injective ((Subtype.ext h).trans e.map_one.symm)))
  let f : fixedSpace σ A → {v : Fin 2 → F // (e a).val.mulVec v = v} :=
    fun w => ⟨E w.val, (hE a w.val).symm.trans (congrArg E (w.property ⟨a,ha⟩))⟩
  have hf : Function.Injective f := by
    intro v w h
    exact Subtype.ext (E.injective (congrArg Subtype.val h))
  have hfixed : Nat.card (fixedSpace σ A) ≤ Nat.card F :=
    (Nat.card_le_card_of_injective f hf).trans (fixedVectors_card_le (e a).val hmat)
  have hcard : Nat.card W = Nat.card F * Nat.card F := by
    rw [Nat.card_congr E.toEquiv,Nat.card_fun,Nat.card_fin,pow_two]
  have hprod : Nat.card F * Nat.card F ≤
      Nat.card (W ⧸ fixedSpace σ A) * Nat.card F := by
    rw [← hcard,Submodule.card_eq_card_quotient_mul_card (fixedSpace σ A)]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (Nat.card (W ⧸ fixedSpace σ A)) hfixed
  exact Nat.le_of_mul_le_mul_right hprod Nat.card_pos

/-- The reverse fixed-index inequality forces an actual Sylow subgroup,
including field order two. -/
theorem marked_sylow_of_fixed_quotient_le_card
    (e : D ≃* SL(2,F)) (σ : Representation (ZMod 2) D W)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (hE : ∀ g w, E (σ g w) = Matrix.mulVec (e g).val (E w))
    {A : Subgroup D} (hne : A ≠ ⊥) (hp : IsPGroup 2 A)
    (hi : Nat.card (W ⧸ fixedSpace σ A) ≤ Nat.card A) :
    Nat.card A = Nat.card F ∧ ∃ S : Sylow 2 D, (S : Subgroup D) = A := by
  let : Finite D := Finite.of_equiv SL(2,F) e.toEquiv.symm
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hScard : Nat.card S = Nat.card F := by
    calc
      Nat.card S = Nat.card T := Nat.card_congr
        ((S : Subgroup D).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
      _ = Nat.card (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2) :=
        Nat.card_congr (T.equiv (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)).toEquiv
      _ = Nat.card F := Matrix.SpecialLinearGroup.card_upperUnipotent F
  have hFA := (marked_field_card_le_fixed_quotient e σ E hE hne).trans hi
  have hAS : A = (S : Subgroup D) := eq_of_le_of_card_ge hS (hScard ▸ hFA)
  exact ⟨hAS ▸ hScard, S, hAS.symm⟩

/-- The non-strict estimate for every nontrivial two-subgroup of the marked
natural action; the subgroup need not be Sylow in advance. -/
theorem marked_two_subgroup_card_le_fixed_quotient
    (e : D ≃* SL(2,F)) (σ : Representation (ZMod 2) D W)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (hE : ∀ g w, E (σ g w) = Matrix.mulVec (e g).val (E w))
    {A : Subgroup D} (hne : A ≠ ⊥) (hp : IsPGroup 2 A) :
    Nat.card A ≤ Nat.card (W ⧸ fixedSpace σ A) := by
  let : Finite D := Finite.of_equiv SL(2,F) e.toEquiv.symm
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hScard : Nat.card S = Nat.card F := by
    calc
      Nat.card S = Nat.card T := Nat.card_congr
        ((S : Subgroup D).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
      _ = Nat.card (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2) :=
        Nat.card_congr (T.equiv (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)).toEquiv
      _ = Nat.card F := Matrix.SpecialLinearGroup.card_upperUnipotent F
  exact ((Nat.card_le_card_of_injective (inclusion hS) (inclusion_injective hS)).trans
    hScard.le).trans (marked_field_card_le_fixed_quotient e σ E hE hne)

end Representation.SL2NaturalOffenders
