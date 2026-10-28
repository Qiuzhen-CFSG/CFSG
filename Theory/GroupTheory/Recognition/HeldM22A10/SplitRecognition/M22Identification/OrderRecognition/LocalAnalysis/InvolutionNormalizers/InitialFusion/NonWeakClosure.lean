module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FusionConstraints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.FusionReduction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.SylowTransport

/-!
# The non-weak-closure step in Janko's initial fusion

The coordinate Sylow subgroup contains the marked involution centrally. Its
weak closure would make that involution central in the simple ambient group
by the proved Z-star corollary. The local centralizer order excludes this.
Thus a distinct conjugate exists in the coordinate Sylow, and the five local
involution classes reduce it to one of the four noncentral representatives.

The coordinate Sylow is not identified with the originally chosen Sylow.
No ambient fusion, normalizer action, or recognition theorem is assumed.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, the paragraph preceding Lemma 5, p.5.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The arbitrary coordinate Sylow lies in the actual marked centralizer. -/
public theorem caseIISylow_le_centralizer :
    (caseIISylow D k : Subgroup G) ≤ D.centralizer := by
  rintro x ⟨v, _, rfl⟩
  exact (k v).property

/-- The marked involution is not weakly closed in the coordinate Sylow. -/
public theorem exists_distinct_caseIISylow_conjugate [IsSimpleGroup G] :
    ∃ t : caseIISylow D k, (t : G) ≠ D.z ∧ IsConj D.z (t : G) := by
  have hzT : D.z ∈ caseIISylow D k := by
    rw [← into_z_zero D k]
    exact E_le_caseIISylow D k (by
      rw [← modelE_map D k]
      exact mem_map_of_mem _ (z_mem_modelE 0))
  let zT : caseIISylow D k := ⟨D.z, hzT⟩
  have hzC : zT ∈ center (caseIISylow D k) := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp
      (caseIISylow_le_centralizer D k x.property))
  by_contra! hw
  apply D.z_not_mem_ambient_center
  apply (caseIISylow D k).weakly_closed_involution_mem_center_of_simple zT
    ((Subgroup.orderOf_coe zT).symm.trans D.z_order) hzC
  intro t ht
  apply Subtype.ext
  by_contra hne
  exact hw t hne ht

/-- Some noncentral coordinate representative fuses to the marked involution.
The first representative cannot occur: it is central in the local model. -/
public theorem initial_fusion_alternatives [IsSimpleGroup G] :
    IsConj D.z (into D k (z 1)) ∨ IsConj D.z (into D k (z 2)) ∨
    IsConj D.z (into D k a) ∨ IsConj D.z (into D k d) := by
  obtain ⟨t, ht, hzt⟩ := exists_distinct_caseIISylow_conjugate D k
  let v := k.symm ⟨(t : G), caseIISylow_le_centralizer D k t.property⟩
  have hv : into D k v = (t : G) :=
    congrArg Subtype.val (k.apply_symm_apply _)
  have ht2 : orderOf (t : G) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hzt
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq D.z).trans D.z_order
  have hv2 : orderOf v = 2 := by
    rw [← orderOf_injective (into D k) (into_injective D k), hv, ht2]
  have hv0 : v ≠ z 0 := by
    intro he
    exact ht (hv.symm.trans ((congrArg (into D k) he).trans (into_z_zero D k)))
  rcases model_involution_classes v hv2 with h | h | h | h | h
  · exact (hv0 (h.eq_of_right_mem_center z_zero_mem_center)).elim
  · exact Or.inl (hzt.trans (hv ▸ (into D k).map_isConj h))
  · exact Or.inr (Or.inl (hzt.trans (hv ▸ (into D k).map_isConj h)))
  · exact Or.inr (Or.inr (Or.inl (hzt.trans (hv ▸ (into D k).map_isConj h))))
  · exact Or.inr (Or.inr (Or.inr (hzt.trans (hv ▸ (into D k).map_isConj h))))

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
