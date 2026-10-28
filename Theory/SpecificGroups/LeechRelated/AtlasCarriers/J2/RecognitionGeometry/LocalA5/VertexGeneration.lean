module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.EdgeEmbedding
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.LocalChecks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.VertexGenerationData
import Mathlib.Tactic.FinCases

/-!
# Generation of the full vertex normalizer

Thirty-six words in the explicit edge and vertex candidates have distinct
conjugates of y. The edge candidate centralizes y and has order sixty, so
multiplying the thirty-six words by its elements gives 2,160 distinct elements
of the generated subgroup. The permitted order hypothesis on the literal M
then makes this subgroup all of M. No normalizer structure is assumed.
Source: Aschbacher, *Sporadic Groups*, 47.5 and 47.10, pp.263, 266–267.
-/

public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
open Subgroup Theory.GroupTheory VertexGenerationData
open GeneratorPair.SecondOrbitCertificate

private def H : Subgroup Carrier := edgeCandidate ⊔ vertexCandidate
private def letters : Fin 4 → Carrier := ![rotation, edgeExtra, x, inverter]
private def rep (i : Fin 36) : Carrier := evalWord letters (word i)

private theorem letterValue_eq (j : Fin 4) (i : Fin 100) :
    letterValue j i = inclusion (letters j) i := by
  fin_cases j
  · exact (EdgeChecks.letterValue_eq 0 i).trans (congrArg (fun p => p i) inclusion_rotation.symm)
  · exact (EdgeChecks.letterValue_eq 1 i).trans (congrArg (fun p => p i) inclusion_edgeExtra.symm)
  · exact (LocalChecks.letterValue_eq 0 i).trans (congrArg (fun p => p i) inclusion_x.symm)
  · exact (LocalChecks.letterValue_eq 2 i).trans (congrArg (fun p => p i) inclusion_inverter.symm)

private theorem wordValue_eq (w : List (Fin 4)) (i : Fin 100) :
    wordValue w i = inclusion (evalWord letters w) i := by
  induction w with
  | nil => rfl
  | cons j w ih => rw [wordValue, ih, letterValue_eq, evalWord, map_mul, Equiv.Perm.mul_apply]

set_option maxRecDepth 20000 in
private theorem rep_value (j : Fin 36) (i : Fin 100) : inclusion (rep j) i = value j i := by
  have h : ∀ j i, wordValue (word j) i = value j i := by
    apply allFin
    decide +kernel
  exact (wordValue_eq (word j) i).symm.trans (h j i)

set_option maxRecDepth 20000 in
private theorem rep_conj_value (j : Fin 36) (i : Fin 100) :
    inclusion (MulAut.conj (rep j) y) i = conjugateValue j i := by
  have h : ∀ j i, value j (LocalIndexed.letterValue 1 i) = conjugateValue j (value j i) := by
    apply allFin
    decide +kernel
  change inclusion (rep j * y * (rep j)⁻¹) i = _
  simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
  rw [rep_value, inclusion_y]
  change value j (LocalData.table 1 ((inclusion (rep j))⁻¹ i)) = _
  rw [← LocalChecks.letterValue_eq, h, ← rep_value]
  simp

private theorem rep_conj_injective : Function.Injective (fun j => MulAut.conj (rep j) y) := by
  have hi : Function.Injective fingerprint := by decide +kernel
  intro i j hij
  apply hi
  apply Prod.ext
  · simpa only [rep_conj_value, VertexGenerationData.fingerprint] using
      congrArg (fun g => inclusion g 0) hij
  · apply Prod.ext
    · simpa only [rep_conj_value, VertexGenerationData.fingerprint] using
        congrArg (fun g => inclusion g 1) hij
    · simpa only [rep_conj_value, VertexGenerationData.fingerprint] using
        congrArg (fun g => inclusion g 3) hij

private theorem rep_mem (i : Fin 36) : rep i ∈ H := by
  have hw (w : List (Fin 4)) : evalWord letters w ∈ H := by
    induction w with
    | nil => exact H.one_mem
    | cons j w ih =>
      apply H.mul_mem _ ih
      fin_cases j
      · exact mem_sup_left (mem_sup_left (mem_zpowers rotation))
      · exact mem_sup_left (mem_sup_right (mem_zpowers edgeExtra))
      · exact mem_sup_right (mem_sup_left (mem_zpowers x))
      · exact mem_sup_right (mem_sup_right (mem_zpowers inverter))
  exact hw _

private theorem edgeCandidate_conj_y {e : Carrier} (he : e ∈ edgeCandidate) :
    MulAut.conj e y = y := by
  have hc : edgeCandidate ≤ centralizer ({y} : Set Carrier) := by
    apply sup_le <;> apply zpowers_le.mpr <;> apply mem_centralizer_singleton_iff.mpr
    · exact mem_centralizer_iff.mp (X_sup_Y_le_K (mem_sup_right (mem_zpowers y)))
        rotation (mem_sup_left (mem_zpowers rotation))
    · exact mul_inv_eq_iff_eq_mul.mp edgeExtra_conj_y
  change e * y * e⁻¹ = y
  rw [mem_centralizer_singleton_iff.mp (hc he), mul_inv_cancel_right]

private def cosetProduct (p : Fin 36 × edgeCandidate) : H :=
  ⟨rep p.1 * p.2, H.mul_mem (rep_mem p.1) (mem_sup_left p.2.property)⟩

private theorem cosetProduct_injective : Function.Injective cosetProduct := by
  rintro ⟨i, e⟩ ⟨j, f⟩ h
  have hc := congrArg (fun g : H => MulAut.conj (g : Carrier) y) h
  change MulAut.conj (rep i * e) y = MulAut.conj (rep j * f) y at hc
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply,
    edgeCandidate_conj_y e.property, edgeCandidate_conj_y f.property] at hc
  have hi := rep_conj_injective hc
  subst j
  have hp := congrArg Subtype.val h
  change rep i * e.val = rep i * f.val at hp
  have hef : e = f := Subtype.ext (mul_left_cancel hp)
  subst f
  rfl

private theorem card_H_ge : 2160 ≤ Nat.card H := by
  have h := Nat.card_le_card_of_injective cosetProduct cosetProduct_injective
  simpa only [Nat.card_prod, Nat.card_fin, card_edgeCandidate] using h

/-- The candidate edge and vertex subgroups fill the literal normalizer. -/
theorem candidates_generate_M (hM : Nat.card M = 2160) :
    edgeCandidate ⊔ vertexCandidate = M := by
  have hle : H ≤ M := sup_le (edgeCandidate_le_E.trans inf_le_left)
    (vertexCandidate_le_K_inf_M.trans inf_le_right)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hM]; exact card_H_ge)

/-- The vertex generation premise of `ConcreteSystem.ofCalculations`. -/
theorem E_sup_K_inf_M (hM : Nat.card M = 2160) : E ⊔ (K ⊓ M) = M := by
  apply le_antisymm (sup_le inf_le_left inf_le_right)
  calc
    M = edgeCandidate ⊔ vertexCandidate := (candidates_generate_M hM).symm
    _ ≤ E ⊔ (K ⊓ M) := sup_le (edgeCandidate_le_E.trans le_sup_left)
      (vertexCandidate_le_K_inf_M.trans le_sup_right)

end Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
