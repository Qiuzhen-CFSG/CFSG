module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.CommonModelStructure
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.Ordinary

/-!
# Whole-normalizer placement for every nontrivial common image

The fixed pure self-centralizing common group bounds the actual double
centralizer even when the image has order two. Its forced central eight
and intrinsic rank criterion distinguish mask 1257. Hence the whole original
normalizer fixes that involution and lies in its native max2 conjugate.
The arbitrary-radical application retains the literal restriction and core
maps. Source: Kleidman--Wilson (1988), Section 2.1, p.489.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
open Cardinality KernelCount QuotientCount.Image
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open NativePair NativePair.Stabilizer LinearFive InvolutionCentralizers.Second
open M22Images.KernelAction InvolutionCentralizers.Second.FiveAction DisplacementActions
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup
  Cardinality.localKernel basis
set_option backward.isDefEq.respectTransparency true

/-- The whole original normalizer fixes the intrinsically distinguished
involution. No maximality is needed for this containment. -/
theorem common_nontrivial_normalizer_le_centralizer (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (hne : (X.subgroupOf M).map starHom ≠ ⊥) :
    normalizer (X : Set Model) ≤ centralizer ({(kernelValue 1257 : Model)} : Set Model) := by
  let Z := centralizer (centralizer (X : Set Model) : Set Model)
  have hb : Z ≤ commonModel := common_double_centralizer_le_model X hpair hpure hpos hne
  have hZ : (kernelValue 1257 : Model) ∈ Z :=
    (common_center_involution_mem X hpair hpure hpos hne).1
  have hz1 : (kernelValue 1257 : Model) ≠ 1 := by
    intro he
    have ho := (common_center_involution_mem X hpair hpure hpos hne).2
    rw [he,orderOf_one] at ho
    contradiction
  have hNZ : normalizer (X : Set Model) ≤ normalizer (Z : Set Model) :=
    (normalizer_le_normalizer_centralizer X).trans
      (normalizer_le_normalizer_centralizer (centralizer (X : Set Model)))
  intro g hg
  have mem_conj (k : Model) (hk : k ∈ normalizer (Z : Set Model))
      (v : Model) (hv : v ∈ Z) : (MulAut.conj k) v ∈ Z := by
    rw [← mem_normalizer_iff_map_conj_eq.mp hk]
    exact mem_map_of_mem (MulAut.conj k).toMonoidHom hv
  have hgz : (MulAut.conj g) (kernelValue 1257 : Model) ∈ Z := mem_conj g (hNZ hg) _ hZ
  have hgz1 : (MulAut.conj g) (kernelValue 1257 : Model) ≠ 1 := by
    intro he
    exact hz1 ((MulAut.conj g).injective (he.trans (map_one _).symm))
  have hfixed : (MulAut.conj g) (kernelValue 1257 : Model) = (kernelValue 1257 : Model) := by
    apply commonModel_rank_unique _ (hb hgz) hgz1
    intro j
    let v : Model := kernelValue (commonCenterMask j)
    have hv : v ∈ Z := common_center_kernel_mem X hpair hpure hpos hne j
    have hw : (MulAut.conj g⁻¹) v ∈ Z := mem_conj _ ((normalizer _).inv_mem (hNZ hg)) v hv
    have hu := commonModel_rank_upper _ (hb hw)
    have hr := pairRank_conj g (kernelValue 1257) ((MulAut.conj g⁻¹) v)
    have he : (MulAut.conj g) ((MulAut.conj g⁻¹) v) = v := by
      simp only [MulAut.conj_apply,inv_inv,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one]
    rw [he] at hr
    exact hr.le.trans hu
  apply mem_centralizer_singleton_iff.mpr
  exact mul_inv_eq_iff_eq_mul.mp hfixed

/-- Literal native max2 placement for every actual nontrivial common-image
extension, with its whole normalizer and a genuine ambient conjugator. -/
theorem common_nontrivial_normalizer_placement (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (hne : (X.subgroupOf M).map starHom ≠ ⊥) :
    ∃ g : Model, normalizer (X : Set Model) ≤
      sourceSubgroup.map (MulAut.conj g).toMonoidHom := by
  have ho := (common_center_involution_mem X hpair hpure hpos hne).2
  have hz1 : (kernelValue 1257 : Model) ≠ 1 := by
    intro h
    rw [h,orderOf_one] at ho
    contradiction
  have hp := commonSpace_pure (kernelValue 1257) ((mem_commonSpace _).mpr ⟨16,rfl⟩) hz1
  obtain ⟨g,hg⟩ := first_line_normalizer (kernelValue 1257) hp
  rw [normalizer_zpowers_eq_centralizer_of_order_two _ ho] at hg
  exact ⟨g,hg ▸ common_nontrivial_normalizer_le_centralizer X hpair hpure hpos hne⟩

/-- At maximal TWO-local level the common-image endpoint is exactly max2. -/
theorem common_nontrivial_maximal (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (hne : (X.subgroupOf M).map starHom ≠ ⊥)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ g : Model, normalizer (X : Set Model) =
      sourceSubgroup.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := common_nontrivial_normalizer_placement X hpair hpure hpos hne
  exact ⟨g,hmax.eq_of_le (sourceSubgroup_isTwoLocal.map_equiv (MulAut.conj g)) hg⟩

/-- The common-image source branch for an arbitrary original radical whose
whole normalizer is controlled by this elementary witness. No center-size
bound is imposed, and all restriction and denominator maps are literal. -/
theorem common_nontrivial_radical (P X : Subgroup Model) (hP : P.IsPRadical 2)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (hne : (X.subgroupOf M).map starHom ≠ ⊥)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ g : Model, let L := sourceSubgroup.map (MulAut.conj g).toMonoidHom
      IsTwoLocal L ∧ normalizer (P : Set Model) ≤ L ∧ P ≤ L ∧
      (normalizer (P.subgroupOf L : Set L)).map L.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf L).IsPRadical 2 ∧
      (normalizer (P.subgroupOf L : Set L)).pCoreIn 2 = P.subgroupOf L ∧
      ((normalizer (P.subgroupOf L : Set L)).pCoreIn 2).map L.subtype = P := by
  obtain ⟨g,hg⟩ := common_nontrivial_normalizer_placement X hpair hpure hpos hne
  let L := sourceSubgroup.map (MulAut.conj g).toMonoidHom
  have hNL : normalizer (P : Set Model) ≤ L := hNX.trans hg
  have hPL := P.le_normalizer.trans hNL
  have hNN := hNL.trans L.le_normalizer
  have hc := hP.normalizer_core_subgroupOf L hPL hNN
  refine ⟨g,sourceSubgroup_isTwoLocal.map_equiv (MulAut.conj g),hNL,hPL,?_,
    hP.subgroupOf_of_normalizer_normalizes L hPL hNN,hc,?_⟩
  · rw [← subgroupOf_normalizer_eq hPL,map_subgroupOf_eq_of_le hNL]
  · rw [hc,map_subgroupOf_eq_of_le hPL]

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
