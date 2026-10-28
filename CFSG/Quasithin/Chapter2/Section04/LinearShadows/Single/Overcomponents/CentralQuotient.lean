module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.Overcomponents.Catalogue
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
/-!
# Restoring the actual central quotient of the surviving model

Centerlessness of the projective quotient forces the entire center into the
two-core. Quasisimplicity supplies the reverse inclusion. The finite-field
isomorphism then identifies the same central quotient with native PSL₃(4).
Source: Aschbacher–Smith 2.4.11, printed p.532.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open scoped MatrixGroups
variable {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
lemma center_and_native_quotient_of_psl_four
    (h : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    center K = pCore 2 K ∧ Nonempty ((K ⧸ center K) ≃* Matrix.PSL3Four.PSL) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  let := Fintype.ofFinite F
  let := Fintype.ofFinite Matrix.PSL3Four.F
  let r : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hF,Matrix.PSL3Four.card_F])
  let e' : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Four.PSL := e.trans (Atlas.fieldEquivPSL 3 r)
  have hbar : center (K ⧸ pCore 2 K) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e' ⟨x,hx⟩).property
    have hz : center Matrix.PSL3Four.PSL = ⊥ :=
      Group.IsPerfect.center_quotient_center_eq_bot (Matrix.SpecialLinearGroup (Fin 3) Matrix.PSL3Four.F)
    change e' x ∈ center Matrix.PSL3Four.PSL at hh
    rw [hz,mem_bot] at hh
    exact e'.injective (hh.trans e'.map_one.symm)
  have hc : center K = pCore 2 K := by
    apply le_antisymm _ (IsQuasisimple.pCore_le_center 2)
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    apply mem_bot.mp
    rw [←hbar]
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) y
    change (QuotientGroup.mk' (pCore 2 K)) a * (QuotientGroup.mk' (pCore 2 K)) x =
      (QuotientGroup.mk' (pCore 2 K)) x * (QuotientGroup.mk' (pCore 2 K)) a
    simpa only [map_mul] using congrArg (QuotientGroup.mk' (pCore 2 K)) (mem_center_iff.mp hx a)
  exact ⟨hc,⟨(QuotientGroup.quotientMulEquivOfEq hc).trans e'⟩⟩
end CFSG.Quasithin.Chapter2.ComponentRefinement
