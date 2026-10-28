module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.LocalCoverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.VertexEmbedding
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.IntersectionData
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.NormalizerPowers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.Reversal
import Mathlib.Tactic.FinCases

/-!
# The literal local intersections

Inside the certified local A₅, normalizing X leaves precisely the six marked
S₃ words. Among these six, only the identity also normalizes Y. Thus the
local pointwise edge fixer is trivial, and its setwise edge stabilizer is
exactly the subgroup of the fixed reversal. These are the literal intersections
used by the uniqueness system, with no unspecified conjugacy choices.
Source: Aschbacher, *Sporadic Groups*, 47.10, pp.266–267.
-/

public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
open Subgroup Theory.GroupTheory GraphUniquenessSystem
open InnerInvolutionCores.NoncentralData IntersectionData
open GeneratorPair.SecondOrbitCertificate

private theorem checkedAt {n : Nat} {f : Fin n → Bool}
    (h : checkFin f = true) (i : Fin n) : f i = true := by
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt] using hi

private theorem xPower_eq (j : Fin 2) (i : Fin 100) :
    inclusion (x ^ (j.val + 1)) i = xPower j i := by
  rw [map_pow, inclusion_x]
  fin_cases j <;> simp only [xPower, zero_add, pow_one,
    Nat.reduceAdd, pow_two, Equiv.Perm.mul_apply, ↓reduceIte]
  · exact (LocalChecks.letterValue_eq 0 i).symm
  · rw [LocalChecks.letterValue_eq, LocalChecks.letterValue_eq]
    rfl

private theorem yPower_eq (j : Fin 2) (i : Fin 100) :
    inclusion (y ^ (j.val + 1)) i = yPower j i := by
  rw [map_pow, inclusion_y]
  fin_cases j <;> simp only [yPower, zero_add, pow_one,
    Nat.reduceAdd, pow_two, Equiv.Perm.mul_apply, ↓reduceIte]
  · exact (LocalChecks.letterValue_eq 1 i).symm
  · rw [LocalChecks.letterValue_eq, LocalChecks.letterValue_eq]
    rfl

set_option maxRecDepth 20000 in
private theorem filter_check (j : Fin 60) (k : Fin 2)
    (h : LocalIndexed.value j (LocalIndexed.letterValue 0 (badPoint j k)) =
      xPower k (LocalIndexed.value j (badPoint j k))) (i : Fin 100) :
    LocalIndexed.value j i = VertexData.value (image j) i := by
  have hc : checkFin (fun j : Fin 60 => checkFin (fun k : Fin 2 =>
      if LocalIndexed.value j (LocalIndexed.letterValue 0 (badPoint j k)) =
          xPower k (LocalIndexed.value j (badPoint j k))
      then checkFin (fun i : Fin 100 => decide
        (LocalIndexed.value j i = VertexData.value (image j) i))
      else true)) = true := by decide +kernel
  have hj := checkedAt (checkedAt hc j) k
  rw [if_pos h] at hj
  exact of_decide_eq_true (checkedAt hj i)

theorem K_inf_M_eq_vertexCandidate : K ⊓ M = vertexCandidate := by
  apply le_antisymm _ vertexCandidate_le_K_inf_M
  intro g hg
  have hgK := hg.1
  rw [K_eq_localCandidate, ← localHom_range] at hgK
  obtain ⟨p, rfl⟩ := hgK
  obtain ⟨j, rfl⟩ := simpleEquiv.surjective p
  change localHom (simpleEnum j) ∈ vertexCandidate
  obtain ⟨k, hk⟩ := normalizer_three_power orderOf_x hg.2
  change localHom (simpleEnum j) * x = x ^ (k.val + 1) * localHom (simpleEnum j) at hk
  have he : localHom (simpleEnum j) = vertexHom (image j) := by
    apply inclusion_injective
    apply Equiv.ext
    intro i
    rw [localHom_value, LocalChecks.value_eq, vertexHom_value]
    apply filter_check j k
    have hp := congrArg (fun g => inclusion g (badPoint j k)) hk
    rw [map_mul, map_mul] at hp
    change inclusion (localHom (simpleEnum j)) (inclusion x (badPoint j k)) =
      inclusion (x ^ (k.val + 1)) (inclusion (localHom (simpleEnum j)) (badPoint j k)) at hp
    rw [localHom_value, localHom_value, LocalChecks.value_eq, LocalChecks.value_eq,
      xPower_eq, inclusion_x] at hp
    simpa only [LocalChecks.letterValue_eq, LocalData.table, Matrix.cons_val_zero] using hp
  rw [he, ← vertexHom_range]
  exact ⟨_, rfl⟩

noncomputable def vertexEquiv : (K ⊓ M : Subgroup Carrier) ≃* Equiv.Perm (Fin 3) :=
  (MulEquiv.subgroupCongr K_inf_M_eq_vertexCandidate).trans vertexCandidateEquiv

theorem vertexEquiv_symm_coe (p : Equiv.Perm (Fin 3)) :
    (vertexEquiv.symm p : Carrier) = vertexHom p := by
  change (vertexCandidateEquiv.symm p : Carrier) = vertexHom p
  exact vertexCandidateEquiv_symm_coe p

theorem card_K_inf_M : Nat.card (K ⊓ M : Subgroup Carrier) = 6 := by
  rw [K_inf_M_eq_vertexCandidate]
  exact card_vertexCandidate

private theorem vertex_normalizes_y (p : Equiv.Perm (Fin 3)) (k : Fin 2)
    (h : ∀ i, VertexData.value p (LocalIndexed.letterValue 1 i) =
      yPower k (VertexData.value p i)) : ∀ i, VertexData.value p i = i := by
  have hc : ∀ (p : Equiv.Perm (Fin 3)) (k : Fin 2),
      (∀ i, VertexData.value p (LocalIndexed.letterValue 1 i) =
        yPower k (VertexData.value p i)) → ∀ i, VertexData.value p i = i := by
    decide +kernel
  exact hc p k h

theorem K_inf_E_eq_bot : K ⊓ E = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  have hgv : g ∈ vertexCandidate := by
    rw [← K_inf_M_eq_vertexCandidate]
    exact ⟨hg.1, hg.2.1⟩
  rw [← vertexHom_range] at hgv
  obtain ⟨p, rfl⟩ := hgv
  have hoy : orderOf y = 3 := ((MulAut.conj conjugator).orderOf_eq x).trans orderOf_x
  obtain ⟨k, hk⟩ := normalizer_three_power hoy hg.2.2
  apply inclusion_injective
  apply Equiv.ext
  intro i
  rw [map_one, vertexHom_value]
  apply vertex_normalizes_y p k
  intro j
  have hp := congrArg (fun g => inclusion g j) hk
  simp only [map_mul, Equiv.Perm.mul_apply] at hp
  rw [vertexHom_value, vertexHom_value, yPower_eq, inclusion_y] at hp
  simpa only [LocalChecks.letterValue_eq, LocalData.table, Matrix.cons_val_one,
    Matrix.cons_val_zero] using hp

/-- The local edge stabilizer is exactly the fixed reversal subgroup. -/
theorem K_inf_edgeStabilizer_eq_zpowers :
    K ⊓ edgeStabilizer Carrier base neighbor = zpowers t := by
  rw [K_inf_edgeStabilizer_eq, K_inf_E_eq_bot, bot_sup_eq]

/-- The local generation premise of `ConcreteSystem.ofCalculations`. -/
theorem local_generate :
    (K ⊓ edgeStabilizer Carrier base neighbor) ⊔ (K ⊓ M) = K := by
  apply le_antisymm (sup_le inf_le_left inf_le_left)
  conv_lhs => rw [K_eq_localCandidate]
  let H : Subgroup Carrier :=
    (K ⊓ edgeStabilizer Carrier base neighbor) ⊔ (K ⊓ M)
  have ht : t ∈ H := mem_sup_left ⟨t_mem_K, t_mem_edgeStabilizer⟩
  have hx : x ∈ H := mem_sup_right
    (vertexCandidate_le_K_inf_M (mem_sup_left (mem_zpowers x)))
  have hs : inverter ∈ H := mem_sup_right
    (vertexCandidate_le_K_inf_M (mem_sup_right (mem_zpowers inverter)))
  have hy : y ∈ H := by
    rw [← t_conj_x]
    exact H.mul_mem (H.mul_mem ht hx) (H.inv_mem ht)
  exact sup_le (sup_le (zpowers_le.mpr hx) (zpowers_le.mpr hy)) (zpowers_le.mpr hs)

end Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
