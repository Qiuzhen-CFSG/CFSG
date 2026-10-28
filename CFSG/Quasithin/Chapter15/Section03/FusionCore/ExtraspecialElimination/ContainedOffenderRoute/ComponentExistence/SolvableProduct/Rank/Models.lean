module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.NonQuasisimple
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# The natural quotient plane of an S₃ factor

An actual S₃ equivalence excludes S₅ by cardinality and SL₃ by perfectness.
The SL₂ order formula then forces its field to have two elements. The
intertwining linear equivalence gives dimension two, and the explicit
matrix with rows (0,1) and (1,1) supplies a cubic fixed-point-free actor.
Both the natural and exceptional alternatives are inspected; no rank or
splitting of the original module is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(3),
printed p.105, as used in the proof of 15.3.49(i), printed pp.1143–1144.
-/

@[expose] public section

open Subgroup Representation
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct.Rank

private theorem sl2_card_two {F : Type*} [Field F] [Finite F]
    (e : SL(2,F) ≃* Equiv.Perm (Fin 3)) : Nat.card F = 2 := by
  have hc : Nat.card F * (Nat.card F ^ 2 - 1) = 6 := by
    rw [← Atlas.card_sl_two, Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hp : 1 < Nat.card F := Finite.one_lt_card
  have hq : Nat.card F ^ 2 = (Nat.card F ^ 2 - 1) + 1 := by
    have : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow 2 _ (by omega)
    omega
  nlinarith

private theorem no_sl3 {F : Type*} [Field F]
    (e : SL(3,F) ≃* Equiv.Perm (Fin 3)) : False := by
  let := Atlas.sl_perfect (F := F) 3 (by decide)
  let : Group.IsPerfect (Equiv.Perm (Fin 3)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have h := Abelianization.commutator_subset_ker (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ)
  rw [Group.IsPerfect.commutator_eq_top] at h
  have hx := h (mem_top (Equiv.swap (0 : Fin 3) 1))
  have hn : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) ≠ 1 := by decide
  exact hn hx

private theorem no_s5 (e : Equiv.Perm (Fin 5) ≃* Equiv.Perm (Fin 3)) : False := by
  have h := Nat.card_congr e.toEquiv
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin, Nat.factorial] at h

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

private theorem natural_plane (h : FactorNatural ρ) (e : D ≃* Equiv.Perm (Fin 3)) :
    ∃ F : BinaryField, Nat.card F.Carrier = 2 ∧ Nonempty (ActionEquiv ρ (linearNatural F 2)) := by
  cases h with
  | linearTwo F h =>
    obtain ⟨a⟩ := h
    exact ⟨F, sl2_card_two (a.groupEquiv.symm.trans e), ⟨a⟩⟩
  | symmetricFive h =>
    obtain ⟨a⟩ := h
    exact (no_s5 (a.groupEquiv.symm.trans e)).elim
  | linearThree F ho h =>
    obtain ⟨a⟩ := h
    exact (no_sl3 (a.groupEquiv.symm.trans e)).elim

private theorem factor_plane {A : Subgroup D} {U : Subrepresentation ρ}
    (h : FactorCase ρ A U) (e : A ≃* Equiv.Perm (Fin 3)) :
    U.toSubmodule = moved ρ A ∧
      ∃ F : BinaryField, Nat.card F.Carrier = 2 ∧ Nonempty
        (ActionEquiv (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype)
          (linearNatural F 2)) := by
  cases h with
  | natural hm h => exact ⟨hm, natural_plane _ h e⟩
  | doubleNatural F ho hm h =>
    obtain ⟨a⟩ := h
    exact (no_sl3 (a.groupEquiv.symm.trans e)).elim
  | exceptional hm h =>
    obtain ⟨_, _, W, _, ⟨a⟩⟩ := h
    exact (no_sl3 (a.groupEquiv.symm.trans e)).elim

private def cubic (F : BinaryField) : SL(2,F.Carrier) :=
  ⟨!![0,1;1,1], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

private theorem cubic_pow (F : BinaryField) : cubic F ^ 3 = 1 := by
  apply Subtype.ext
  change (!![0,1;1,1] : Matrix (Fin 2) (Fin 2) F.Carrier) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

private theorem cubic_fixed (F : BinaryField) (v : Fin 2 → F.Carrier)
    (hv : linearNatural F 2 (cubic F) v = v) : v = 0 := by
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  change (cubic F).val.mulVec v 0 = v 0 at h0
  change (cubic F).val.mulVec v 1 = v 1 at h1
  simp [cubic, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have hz0 : v 0 = 0 := h1
  ext i
  fin_cases i
  · exact hz0
  · exact h0.trans hz0

/-- The surviving module is a plane and has an actual cubic fixed-point-free actor. -/
private theorem plane_data (F : BinaryField) (hc : Nat.card F.Carrier = 2)
    (a : ActionEquiv ρ (linearNatural F 2)) :
    Module.finrank (ZMod 2) V = 2 ∧
      ∃ r : D, r ^ 3 = 1 ∧ ∀ v : V, ρ r v = v → v = 0 := by
  constructor
  · rw [a.linearEquiv.finrank_eq]
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Fin 2 → F.Carrier)
    rw [Nat.card_fun, hc, Nat.card_fin, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (by decide : 1 < 2)) h.symm
  · refine ⟨a.groupEquiv.symm (cubic F), ?_, ?_⟩
    · rw [← map_pow, cubic_pow, map_one]
    · intro v hv
      apply a.linearEquiv.injective
      rw [map_zero]
      apply cubic_fixed
      have hh := a.intertwines (a.groupEquiv.symm (cubic F)) v
      rw [hv, a.groupEquiv.apply_symm_apply] at hh
      exact hh.symm

/-- For an actual S₃ factor, only the natural binary plane survives. The
image is taken modulo the global fixed space, exactly as in B.5.6(3). -/
theorem factor_quotient_plane {A : Subgroup D} {U : Subrepresentation ρ}
    (h : FactorCase ρ A U) (e : A ≃* Equiv.Perm (Fin 3)) :
    U.toSubmodule = moved ρ A ∧
      Module.finrank (ZMod 2) ((fixed ρ).quotientImage U).toSubmodule = 2 ∧
      ∃ r : A, r ^ 3 = 1 ∧ ∀ v : ((fixed ρ).quotientImage U).toSubmodule,
        ((fixed ρ).quotientImage U).toRepresentation (r : D) v = v → v = 0 := by
  obtain ⟨hm, F, hc, ⟨a⟩⟩ := factor_plane ρ h e
  exact ⟨hm, plane_data _ F hc a⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct.Rank
