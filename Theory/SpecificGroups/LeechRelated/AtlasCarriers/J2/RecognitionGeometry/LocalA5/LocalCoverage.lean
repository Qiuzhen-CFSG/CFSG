module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.LocalEmbedding
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.EdgeChecks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.LocalCoverageData

/-!
# The full centralizer of the marked dihedral group is A₅

The reflection is exactly the involution of the existing 1,920-element
centralizer certificate. A single-point rejection test for commuting with
the rotation leaves precisely the sixty already embedded local elements.
Thus the isomorphism is on the full literal centralizer, not just a candidate.
Source: Aschbacher, *Sporadic Groups*, 47.2 and 47.10, pp.261, 266–267.
-/

public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
open Subgroup Theory.GroupTheory GeneratorPair
open InnerInvolutionCores.NoncentralData LocalCoverageData
open GeneratorPair.SecondOrbitCertificate

private theorem checkedAt {n : Nat} {f : Fin n → Bool}
    (h : checkFin f = true) (i : Fin n) : f i = true := by
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt] using hi

theorem reflection_eq_firstInvolution : reflection = FirstFusion.t := by
  apply inclusion_injective
  rw [inclusion_reflection, FirstFusion.inclusion_t]
  decide +kernel

set_option maxRecDepth 20000 in
private theorem filter_check (j : Fin 1920)
    (h : FirstFusion.LocalCertificate.value j (EdgeIndexed.letterValue 0 (badPoint j)) =
      EdgeIndexed.letterValue 0 (FirstFusion.LocalCertificate.value j (badPoint j)))
    (i : Fin 100) :
    FirstFusion.LocalCertificate.value j i = LocalIndexed.value (imageIndex j) i := by
  have hc : checkFin (fun j : Fin 1920 =>
      if FirstFusion.LocalCertificate.value j (EdgeIndexed.letterValue 0 (badPoint j)) =
          EdgeIndexed.letterValue 0 (FirstFusion.LocalCertificate.value j (badPoint j))
      then checkFin (fun i : Fin 100 => decide
        (FirstFusion.LocalCertificate.value j i = LocalIndexed.value (imageIndex j) i))
      else true) = true := by decide +kernel
  have hj := checkedAt hc j
  rw [if_pos h] at hj
  exact of_decide_eq_true (checkedAt hj i)

/-- Exhaustive coverage of the full centralizer by the fixed local A₅ words. -/
theorem K_le_localCandidate : K ≤ localCandidate := by
  intro g hg
  have hr : reflection ∈ B := mem_sup_right (mem_zpowers reflection)
  have hgC : g ∈ FirstFusion.centralizer := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← reflection_eq_firstInvolution]
    exact (mem_centralizer_iff.mp hg reflection hr).symm
  obtain ⟨j, rfl⟩ := FirstFusion.LocalCertificate.cover g hgC
  have hrot := mem_centralizer_iff.mp hg rotation (mem_sup_left (mem_zpowers rotation))
  have he : FirstFusion.centralizerElement j = localHom (simpleEnum (imageIndex j)) := by
    apply inclusion_injective
    apply Equiv.ext
    intro i
    rw [FirstFusion.LocalCertificate.value_spec, localHom_value, LocalChecks.value_eq]
    apply filter_check
    have hp := congrArg (fun g => inclusion g (badPoint j)) hrot.symm
    simpa only [map_mul, Equiv.Perm.mul_apply, FirstFusion.LocalCertificate.value_spec,
      inclusion_rotation, EdgeChecks.letterValue_eq, EdgeData.table, Matrix.cons_val_zero] using hp
  rw [he, ← localHom_range]
  exact ⟨_, rfl⟩

theorem K_eq_localCandidate : K = localCandidate :=
  le_antisymm K_le_localCandidate localCandidate_le_K

/-- A multiplicative equivalence on the unchanged full local centralizer. -/
noncomputable def localEquiv : K ≃* alternatingGroup (Fin 5) :=
  (MulEquiv.subgroupCongr K_eq_localCandidate).trans localCandidateEquiv

theorem localEquiv_symm_coe (p : alternatingGroup (Fin 5)) :
    (localEquiv.symm p : Carrier) = localHom p := by
  change (localCandidateEquiv.symm p : Carrier) = localHom p
  exact localCandidateEquiv_symm_coe p

theorem card_K : Nat.card K = 60 := by
  rw [K_eq_localCandidate]
  exact card_localCandidate

end Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
