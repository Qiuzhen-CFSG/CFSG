module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.EdgeEmbedding
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.LocalChecks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.EdgeCoverageData
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.NormalizerPowers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.Reversal
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

/-!
# The full pointwise edge fixer is A₅

The fixed reversal is conjugate to a. Every edge fixer centralizes it, so
the existing 240-word certificate covers the conjugated fixer. Normalizing
X eliminates all but the sixty elements of the explicit edge A₅. This proves
an isomorphism on the literal intersection of endpoint normalizers.
Source: Aschbacher, *Sporadic Groups*, 47.5 and 47.10, pp.263, 266–267.
-/

public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
open Subgroup Theory.GroupTheory GeneratorPair
open InnerInvolutionCores.NoncentralData EdgeCoverageData
open GeneratorPair.SecondOrbitCertificate

private theorem checkedAt {n : Nat} {f : Fin n → Bool}
    (h : checkFin f = true) (i : Fin n) : f i = true := by
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt] using hi

private theorem inclusion_move : inclusion move = moveTable :=
  (inclusion_word moveWord).trans (by decide +kernel)

private theorem move_conj_a : move * a * move⁻¹ = t := by
  apply inclusion_injective
  simp only [t, map_mul, map_inv, inclusion_move, inclusion_x, inclusion_y,
    (show inclusion a = tableA from generatorA_eq_table)]
  decide +kernel

private theorem moved_value (j : Fin 240) (i : Fin 100) :
    inclusion (move * SecondOrbitCertificate.conjugator j * move⁻¹) i = value j i := by
  have h : ∀ i : Fin 100, moveTable i = moveValue i ∧ moveTable⁻¹ i = moveInvValue i := by
    decide +kernel
  simp only [map_mul, map_inv, inclusion_move, conjugator_inclusion, Equiv.Perm.mul_apply,
    value, (h _).1, (h _).2]
  rfl

private theorem xPower_eq (j : Fin 2) (i : Fin 100) :
    inclusion (x ^ (j.val + 1)) i = xPower j i := by
  rw [map_pow, inclusion_x]
  fin_cases j <;> simp only [xPower, zero_add, pow_one,
    Nat.reduceAdd, pow_two, Equiv.Perm.mul_apply, ↓reduceIte]
  · exact (LocalChecks.letterValue_eq 0 i).symm
  · rw [LocalChecks.letterValue_eq, LocalChecks.letterValue_eq]
    rfl

set_option maxRecDepth 20000 in
private theorem filter_check (j : Fin 240) (k : Fin 2)
    (h : value j (LocalIndexed.letterValue 0 (badPoint j k)) =
      xPower k (value j (badPoint j k))) (i : Fin 100) :
    value j i = EdgeIndexed.value (imageIndex j) i := by
  have hc : checkFin (fun j : Fin 240 => checkFin (fun k : Fin 2 =>
      if value j (LocalIndexed.letterValue 0 (badPoint j k)) =
          xPower k (value j (badPoint j k))
      then checkFin (fun i : Fin 100 => decide
        (value j i = EdgeIndexed.value (imageIndex j) i))
      else true)) = true := by decide +kernel
  have hj := checkedAt (checkedAt hc j) k
  rw [if_pos h] at hj
  exact of_decide_eq_true (checkedAt hj i)

/-- Exhaustive coverage of the full edge fixer by the fixed edge A₅ words. -/
theorem E_le_edgeCandidate : E ≤ edgeCandidate := by
  intro g hg
  have hc : move⁻¹ * g * move ∈ centralizer ({a} : Set Carrier) := by
    apply mem_centralizer_singleton_iff.mpr
    have hcomm := mem_centralizer_iff.mp t_mem_centralizer_E g hg
    rw [← move_conj_a] at hcomm
    have hh := congrArg (fun q : Carrier => move⁻¹ * q * move) hcomm
    group at hh ⊢
    exact hh
  obtain ⟨j, hj⟩ := InnerInvolutionCores.a_centralizer_cover _ hc
  have hgval : g = move * SecondOrbitCertificate.conjugator j * move⁻¹ := by
    rw [← hj]
    group
  obtain ⟨k, hk⟩ := normalizer_three_power orderOf_x hg.1
  have he : g = edgeHom (simpleEnum (imageIndex j)) := by
    apply inclusion_injective
    apply Equiv.ext
    intro i
    rw [hgval, moved_value, edgeHom_value, EdgeChecks.value_eq]
    apply filter_check j k
    have hp := congrArg (fun q => inclusion q (badPoint j k)) hk
    rw [map_mul, map_mul] at hp
    change inclusion g (inclusion x (badPoint j k)) =
      inclusion (x ^ (k.val + 1)) (inclusion g (badPoint j k)) at hp
    rw [hgval, moved_value, moved_value, xPower_eq, inclusion_x] at hp
    simpa only [LocalChecks.letterValue_eq, LocalData.table, Matrix.cons_val_zero] using hp
  rw [he, ← edgeHom_range]
  exact ⟨_, rfl⟩

theorem E_eq_edgeCandidate : E = edgeCandidate :=
  le_antisymm E_le_edgeCandidate edgeCandidate_le_E

/-- The genuine A₅ isomorphism on the literal edge fixer. -/
noncomputable def edgeEquiv : E ≃* alternatingGroup (Fin 5) :=
  (MulEquiv.subgroupCongr E_eq_edgeCandidate).trans edgeCandidateEquiv

theorem edgeEquiv_symm_coe (p : alternatingGroup (Fin 5)) :
    (edgeEquiv.symm p : Carrier) = edgeHom p := by
  change (edgeCandidateEquiv.symm p : Carrier) = edgeHom p
  exact edgeCandidateEquiv_symm_coe p

theorem card_E : Nat.card E = 60 := by
  rw [E_eq_edgeCandidate]
  exact card_edgeCandidate

end Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
