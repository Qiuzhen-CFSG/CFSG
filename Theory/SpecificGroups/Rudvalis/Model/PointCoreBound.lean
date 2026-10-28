module
public import Theory.GroupTheory.SylowKernelCore
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix
public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.SylowCenters

import all Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.LocalOrder.Separation

/-!
# No elementary sixty-four in a Rudvalis involution-centralizer core

The preserved Sylow normal forms have a kernel-checked 64-label separation
certificate. Label 36 has no representative in the ambient point core:
twenty-one explicit point witnesses show that its entries move one of the
five blocks defining the actual S₅ quotient. An elementary subgroup of order
64 would map bijectively to all 64 labels, a contradiction.

The marked Sylow centralizes the original involution. Its two-point decoder
reduces the generator commutation checks to 28 point equations, after one
normal-form marking. The actual quotient kernel transports block preservation
to every element of the ambient two-core. Conjugacy then gives the bound for
every member of the central involution class, with no hypothesis about a
source Sylow placement.

This is an intentional internal extension of LocalOrder.Separation: its
private decoder certificate is reused through import all, preserving its
existing public boundary. The only new finite data are the displayed witness
points, checked directly against the original ATLAS permutation tables.

The original E₆₄ application is OriginalOddNormalizer.RudvalisModuleIntersection.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612. Attribution and action
conventions are retained in Model.PermutationData and TwoRankSix/source/README.md.
-/

public section
open scoped IsMulCommutative
namespace Rudvalis.PointCoreBound
open Subgroup SylowOvergroups
open SylowOvergroups.RadicalCoverage.SylowCertificate
open SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder
open SylowOvergroups.RadicalCoverage.LocalCover
open Max6Certificate CoreQuotients.Max6Blocks

private theorem candidate_ext (x y : Model) (hx : x ∈ candidate) (hy : y ∈ candidate)
    (h0 : x • (0 : Fin 4060) = y • (0 : Fin 4060))
    (h1 : x • (1 : Fin 4060) = y • (1 : Fin 4060)) : x = y := by
  obtain ⟨n,rfl⟩ := exists_candidateNormalForm hx
  obtain ⟨m,rfl⟩ := exists_candidateNormalForm hy
  have hn : n = m := by
    apply Fin.ext
    rw [normal_smul,normal_smul] at h0 h1
    rw [←decode_normalMap n,←decode_normalMap m,h0,h1]
  rw [hn]

set_option maxRecDepth 30000 in
private theorem zero_normal_form : candidateNormalForm 6144 = elementaryGenerator 0 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change candidateNormalForm 6144 • x = (elementaryGenerator 0).val x
  rw [normal_smul,elementary_zero_val]
  exact (by
    apply Rudvalis.Data.allFin
    decide +kernel : ∀ x : Fin 4060, normalMap 6144 x = AlignmentData.zeroMap x) x

private theorem zero_smul (x : Fin 4060) :
    elementaryGenerator 0 • x = AlignmentData.zeroMap x :=
  Equiv.congr_fun elementary_zero_val x

private theorem generators_fix_zero : ∀ i : Fin 14,
    generatorMap i (AlignmentData.zeroMap 0) = AlignmentData.zeroMap (generatorMap i 0) ∧
    generatorMap i (AlignmentData.zeroMap 1) = AlignmentData.zeroMap (generatorMap i 1) := by
  decide +kernel

private theorem candidate_le_point_centralizer : candidate ≤ centralizer ({elementaryGenerator 0} : Set Model) := by
  have hz : elementaryGenerator 0 ∈ candidate := zero_normal_form ▸ candidateNormalForm_mem 6144
  apply (closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have hi : candidateGenerator i ∈ candidate := subset_closure ⟨i,rfl⟩
  apply candidate_ext _ _ (candidate.mul_mem hi hz) (candidate.mul_mem hz hi)
  · simpa only [mul_smul,generator_smul,zero_smul] using (generators_fix_zero i).1
  · simpa only [mul_smul,generator_smul,zero_smul] using (generators_fix_zero i).2

private def alignedBlock (i : Fin 5) : Finset (Fin 4060) :=
  (block i).map AlignmentData.gapPerm.symm.toEmbedding

private def witnessBlock : Fin 21 → Fin 5 := ![1,1,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
private def witnessPoint : Fin 21 → Fin 4060 := ![460,460,128,128,460,460,460,460,460,460,460,460,460,460,460,460,460,460,460,460,460]
set_option maxRecDepth 30000 in
private theorem witness_check : ∀ s : Fin 21,
    witnessPoint s ∈ alignedBlock (witnessBlock s) ∧
      normalMap (TwoRankSix.entry 36 s) (witnessPoint s) ∉ alignedBlock (witnessBlock s) := by
  decide +kernel

private theorem missing_label (s : Fin 21) :
    ∃ i : Fin 5, ∃ x ∈ alignedBlock i,
      normalMap (TwoRankSix.entry 36 s) x ∉ alignedBlock i :=
  ⟨witnessBlock s,witnessPoint s,(witness_check s).1,(witness_check s).2⟩

private theorem conjugator_val : conjugator.val = AlignmentData.gapPerm.symm := by
  change gapConjugator.val⁻¹ = _
  rw [gapConjugator_val]
  rfl

private theorem map_point_centralizer {X : Type*} [Group X] (e : MulAut X) (z : X) :
    (centralizer ({z} : Set X)).map e.toMonoidHom = centralizer ({e z} : Set X) := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul,MulEquiv.coe_toMonoidHom] using
      congrArg e (mem_centralizer_singleton_iff.mp hu)
  · intro hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul,MulEquiv.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx

private theorem aligned_max6_eq : max6.map (MulAut.conj conjugator).toMonoidHom =
    centralizer ({elementaryGenerator 0} : Set Model) := by
  rw [LowCentralizers.max6_eq_centralizer,map_point_centralizer,conjugator_alignment]

private theorem core_preserves_blocks (x : Model)
    (hx : x ∈ (centralizer ({elementaryGenerator 0} : Set Model)).pCoreIn 2)
    (i : Fin 5) (y : Fin 4060) (hy : y ∈ alignedBlock i) : x • y ∈ alignedBlock i := by
  let t := MulAut.conj conjugator
  have hmap := map_pCoreIn_of_injective 2 max6 t.toMonoidHom t.injective
  rw [aligned_max6_eq] at hmap
  rw [←hmap] at hx
  obtain ⟨u,⟨v,hv,rfl⟩,rfl⟩ := hx
  have hvk : CoreQuotients.max6FiveAction ⟨v,v.property⟩ = 1 := by
    change v ∈ CoreQuotients.max6FiveAction.ker
    rwa [CoreQuotients.max6FiveAction_ker]
  obtain ⟨t,ht,rfl⟩ := Finset.mem_map.mp hy
  have ht' : (v : Model) • t ∈ block i := by
    have hh := CoreQuotients.max6FiveAction_blocks v i
    rw [hvk] at hh
    exact hh ▸ Finset.mem_map.mpr ⟨t,ht,rfl⟩
  apply Finset.mem_map.mpr
  refine ⟨(v : Model) • t,ht',?_⟩
  change AlignmentData.gapPerm.symm ((v : Model) • t) =
    (conjugator * (v : Model) * conjugator⁻¹) • (AlignmentData.gapPerm.symm t)
  rw [←conjugator_val]
  change conjugator • ((v : Model) • t) =
    (conjugator * (v : Model) * conjugator⁻¹) • (conjugator • t)
  simp only [mul_smul,inv_smul_smul]

private theorem core_elementary_not_sixtyFour (E : Subgroup Model)
    [IsElementaryAbelian 2 E]
    (hE : E ≤ (centralizer ({elementaryGenerator 0} : Set Model)).pCoreIn 2)
    (hc : Nat.card E = 64) : False := by
  have hi : ¬ 2 ∣ candidate.index := by
    intro hi
    apply not_two_pow_fifteen_dvd_card_model
    rw [←candidate.card_mul_index,candidate_card]
    exact Nat.mul_dvd_mul_left 16384 hi
  let S : Sylow 2 Model := candidate_isTwoGroup.toSylow hi
  have hCand : (centralizer ({elementaryGenerator 0} : Set Model)).pCoreIn 2 ≤ candidate := by
    have hh := pCoreIn_le_sylow _ (S.subtype candidate_le_point_centralizer)
    change (centralizer ({elementaryGenerator 0} : Set Model)).pCoreIn 2 ≤
      (candidate.subgroupOf (centralizer ({elementaryGenerator 0} : Set Model))).map
        (centralizer ({elementaryGenerator 0} : Set Model)).subtype at hh
    rwa [map_subgroupOf_eq_of_le candidate_le_point_centralizer] at hh
  classical
  let n : E → Fin 16384 := fun x => Classical.choose (exists_candidateNormalForm (hCand (hE x.property)))
  have hn (x : E) : candidateNormalForm (n x) = (x : Model) :=
    Classical.choose_spec (exists_candidateNormalForm (hCand (hE x.property)))
  have hs (x : E) : candidateNormalForm (n x)^2=1 := by
    rw [hn]
    exact elemPow_eq_one_of_isElementaryAbelian x.val x.property
  have hf : Function.Injective (fun x : E => TwoRankSix.label (n x)) := by
    intro x y hxy
    apply Subtype.ext
    have hh := TwoRankSix.index_eq_of_commute_of_label_eq (n x) (n y) (hs x) (hs y)
      (by rw [hn,hn]; exact setLike_mul_comm x.property y.property) hxy
    rw [←hn x,←hn y,hh]
  have hsurj := (hf.bijective_of_nat_card_le (by rw [hc,Nat.card_fin])).surjective
  obtain ⟨x,hx⟩ := hsurj 36
  obtain ⟨i,y,hy,hbad⟩ := missing_label (TwoRankSix.slot (n x))
  have he : TwoRankSix.entry 36 (TwoRankSix.slot (n x)) = n x := by
    rw [←hx,TwoRankSix.entry_of_square_eq_one _ (hs x)]
  rw [he,←normal_smul,hn] at hbad
  exact hbad (core_preserves_blocks x (hE x.property) i y hy)


/-- The actual two-core of a central-class involution centralizer contains
no elementary subgroup of order 64. -/
theorem elementary_not_le_point_core (z : Model) (hz : IsConj z (b^2))
    (E : Subgroup Model) [IsElementaryAbelian 2 E] (hcard : Nat.card E = 64) :
    ¬ E ≤ (centralizer ({z} : Set Model)).pCoreIn 2 := by
  intro hE
  have hlocal : IsConj centralInvolution (elementaryGenerator 0) :=
    isConj_iff.mpr ⟨conjugator,conjugator_alignment⟩
  have hsquare : IsConj centralInvolution (b^2) :=
    isConj_iff.mpr ⟨LowCentralizers.squareConjugator,LowCentralizers.squareConjugator_alignment⟩
  have h0 : IsConj (elementaryGenerator 0) (b^2) := hlocal.symm.trans hsquare
  obtain ⟨g,hg⟩ := isConj_iff.mp (hz.trans h0.symm)
  let t := MulAut.conj g
  have hD : (centralizer ({z} : Set Model)).map t.toMonoidHom =
      centralizer ({elementaryGenerator 0} : Set Model) := by
    rw [map_point_centralizer]
    change t z = elementaryGenerator 0 at hg
    rw [hg]
  let : IsElementaryAbelian 2 (E.map t.toMonoidHom) := IsElementaryAbelian.map _
  apply core_elementary_not_sixtyFour (E.map t.toMonoidHom)
  · have hh := map_mono (f := t.toMonoidHom) hE
    rwa [map_pCoreIn_of_injective 2 _ _ t.injective,hD] at hh
  · rw [card_map_of_injective t.injective,hcard]

end Rudvalis.PointCoreBound
