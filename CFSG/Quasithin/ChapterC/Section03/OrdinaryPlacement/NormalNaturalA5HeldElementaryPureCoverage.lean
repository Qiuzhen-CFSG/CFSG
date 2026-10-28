module
public import Theory.ElementaryAbelian.Basic
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryPureCertificate
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryProducts
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryCertificate

/-! The checked pure-vertex coverage applied to a genuine Held subgroup. -/
public section
open Subgroup
open scoped IsMulCommutative
namespace Held.OrdinaryElementary
open NativeCoverage LocalPairs.SylowGeometry.Calculations
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration

theorem pure_sixteen_mask_of_le (E : Subgroup He) [IsElementaryAbelian 2 E]
    (hE : Nat.card E=16) (hpure : ∀x:E,¬IsConj a (x:He))
    (hEP : E≤representative) :
    ∃j : Fin 8,∀x:E,∃v : Fin 192,
      (candidateMask (pureTarget j)).testBit v.val=true ∧ (native v).val=x.val := by
  classical
  let s : Finset (Fin 192) := Finset.univ.filter (fun v => (native v).val ∈ E)
  have hs (v : Fin 192) : v∈s ↔ (native v).val∈E := by simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]
  have hcover (x : E) : ∃v,(native v).val=x.val := by
    have hp : (⟨x.val,hEP x.property⟩ : representative)^2=1 := by
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian x.val x.property
    obtain ⟨v,hv⟩ := vertex_of_square _ hp
    exact ⟨v,congrArg Subtype.val hv⟩
  have hninj : Function.Injective (fun v => (native v).val) :=
    representative.subtype_injective.comp native_injective
  let f : s → E := fun v => ⟨(native v.val).val,(hs _).mp v.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w he
      exact Subtype.ext (hninj (congrArg (fun x : E => x.val) he))
    · intro x
      obtain ⟨v,hv⟩ := hcover x
      exact ⟨⟨v,(hs v).mpr (hv.symm ▸ x.property)⟩,Subtype.ext hv⟩
  have hcard : s.card=16 := by
    rw [←Nat.card_eq_finsetCard]
    exact (Nat.card_congr (Equiv.ofBijective f hf)).trans hE
  have h0 : 0∈s := by
    apply (hs 0).mpr
    change (normalForm 0).val ∈ E
    rw [Held.InvolutionFixedData.Coverage.normalForm_zero]
    exact E.one_mem
  have hcomm : ∀v∈s,∀w∈s,compatible v w=true := by
    intro v hv w hw
    apply native_compatible
    apply Subtype.ext
    exact setLike_mul_comm ((hs v).mp hv) ((hs w).mp hw)
  have hcoset : ∀v w,w∈s → compatible v w=true → (productVertex v w∈s ↔ v∈s) := by
    intro v w hw hc
    rw [hs,hs,native_product v w hc]
    change (native v).val*(native w).val∈E ↔ (native v).val∈E
    exact E.mul_mem_cancel_right ((hs w).mp hw)
  obtain ⟨k,hk⟩ := clique_coverage s (by omega) hcomm
  have hsub : s⊆purePossible k := by
    intro v hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk v hv,?_⟩
    intro hA
    exact hpure ⟨(native v).val,(hs v).mp hv⟩ ((classA_iff _).mp hA)
  obtain ⟨j,hj⟩ := pure_candidate_coverage k s hcard h0 hsub hcomm hcoset
  refine ⟨j,?_⟩
  intro x
  obtain ⟨v,hv⟩ := hcover x
  refine ⟨v,?_,hv⟩
  exact (Finset.mem_filter.mp (hj ((hs v).mpr (hv.symm ▸ x.property)))).2

end Held.OrdinaryElementary
