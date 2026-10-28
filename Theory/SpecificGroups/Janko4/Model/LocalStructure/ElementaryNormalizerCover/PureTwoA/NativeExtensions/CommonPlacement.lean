module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.CommonRankGeometry
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.Ordinary

/-!
# Whole-normalizer placement for the common four-image

The actual double centralizer contains the forced central eight and lies
in the pure completion. Its intrinsic rank criterion therefore has a unique
nonidentity solution, mask 1257. Simultaneous conjugation preserves the
criterion, so the WHOLE original normalizer fixes that involution. Its
centralizer is a literal conjugate of the native max2 subgroup.

This discharges the common order-four source branch without a selected-lift
invariance assumption or a container callback. The final radical application
retains the actual conjugator, restricted normalizer and embedded core maps.
Source: Kleidman--Wilson (1988), Section 2.1, p.489.
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
theorem common_four_normalizer_le_centralizer (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4) :
    normalizer (X : Set Model) ≤ centralizer ({(kernelValue 1257 : Model)} : Set Model) := by
  have himage := pure_position_image_eq X hpair hpure 1 hpos hfour
  have hn : (X.subgroupOf M).map starHom ≠ ⊥ := by
    intro h
    rw [h,card_bot] at hfour
    contradiction
  let Z := centralizer (centralizer (X : Set Model) : Set Model)
  have hb : Z ≤ commonCompletion X := (common_double_centralizer_bounds X hpair himage).2
  have hZ : (kernelValue 1257 : Model) ∈ Z :=
    (common_center_involution_mem X hpair hpure hpos hn).1
  have hz1 : (kernelValue 1257 : Model) ≠ 1 := by
    intro he
    have ho := (common_center_involution_mem X hpair hpure hpos hn).2
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
    apply commonCompletion_rank_unique X hpair hpure himage _ (hb hgz) hgz1
    intro j
    let v : Model := kernelValue (commonCenterMask j)
    have hv : v ∈ Z := common_center_kernel_mem X hpair hpure hpos hn j
    have hw : (MulAut.conj g⁻¹) v ∈ Z := mem_conj _ ((normalizer _).inv_mem (hNZ hg)) v hv
    have hu := commonCompletion_rank_upper X hpair hpure himage _ (hb hw)
    have hr := pairRank_conj g (kernelValue 1257) ((MulAut.conj g⁻¹) v)
    have he : (MulAut.conj g) ((MulAut.conj g⁻¹) v) = v := by
      simp only [MulAut.conj_apply,inv_inv,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one]
    rw [he] at hr
    exact hr.le.trans hu
  apply mem_centralizer_singleton_iff.mpr
  exact mul_inv_eq_iff_eq_mul.mp hfixed

/-- Literal native max2 placement for every actual common order-four
extension, with its whole normalizer and a genuine ambient conjugator. -/
theorem common_four_normalizer_placement (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4) :
    ∃ g : Model, normalizer (X : Set Model) ≤
      sourceSubgroup.map (MulAut.conj g).toMonoidHom := by
  have hn : (X.subgroupOf M).map starHom ≠ ⊥ := by
    intro h
    rw [h,card_bot] at hfour
    contradiction
  have ho := (common_center_involution_mem X hpair hpure hpos hn).2
  have hz1 : (kernelValue 1257 : Model) ≠ 1 := by
    intro h
    rw [h,orderOf_one] at ho
    contradiction
  have hp := commonSpace_pure (kernelValue 1257) ((mem_commonSpace _).mpr ⟨16,rfl⟩) hz1
  obtain ⟨g,hg⟩ := first_line_normalizer (kernelValue 1257) hp
  rw [normalizer_zpowers_eq_centralizer_of_order_two _ ho] at hg
  exact ⟨g,hg ▸ common_four_normalizer_le_centralizer X hpair hpure hpos hfour⟩

/-- At maximal TWO-local level the common-image endpoint is exactly max2. -/
theorem common_four_maximal (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ g : Model, normalizer (X : Set Model) =
      sourceSubgroup.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := common_four_normalizer_placement X hpair hpure hpos hfour
  exact ⟨g,hmax.eq_of_le (sourceSubgroup_isTwoLocal.map_equiv (MulAut.conj g)) hg⟩

private theorem map_conj_mul (A : Subgroup Model) (g k : Model) :
    (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*k)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem map_conj_one (A : Subgroup Model) :
    A.map (MulAut.conj (1 : Model)).toMonoidHom = A :=
  mem_normalizer_iff_map_conj_eq.mp (normalizer (A : Set Model)).one_mem

/-- The original proper-extension reduction now closes the common four-image
branch. Every remaining case has image order two or exceptional image order
four; purity, maximality, properness and BOTH whole-group transports survive. -/
theorem maximal_pure_extension_after_common_four (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X) (hlarge : 4 < Nat.card X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    (∃ k : Model, normalizer (X : Set Model) =
      sourceSubgroup.map (MulAut.conj k).toMonoidHom) ∨
    ∃ g : localPairCentralizer,
      let Y := X.map (MulAut.conj (g.val : Model)).toMonoidHom
      nativePair ≤ Y ∧ 4 < Nat.card Y ∧ Y ≤ M ∧
      centralizer (Y : Set Model) ≤ M ∧
      (∀ y ∈ Y, y ≠ 1 → IsConj a y) ∧
      IsMaximalTwoLocal (normalizer (Y : Set Model)) ∧
      ((Nat.card ((Y.subgroupOf M).map starHom) = 2 ∧
          ((Y.subgroupOf M).map starHom ≤ imageBlock 0 ∨
            (Y.subgroupOf M).map starHom ≤ imageBlock 1)) ∨
        (Nat.card ((Y.subgroupOf M).map starHom) = 4 ∧
          (Y.subgroupOf M).map starHom ≤ imageBlock 0)) ∧
      centralizer (Y : Set Model) = (centralizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)).toMonoidHom ∧
      normalizer (Y : Set Model) = (normalizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)).toMonoidHom := by
  obtain ⟨g,hP,hlargeY,hM,hC,hpY,hmY,hpos,hsize,hct,hnt⟩ :=
    maximal_pure_extension_two_positions X hpair hlarge hpure hmax
  let Y := X.map (MulAut.conj (g.val : Model)).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  rcases hsize with htwo | hfour
  · exact Or.inr ⟨g,hP,hlargeY,hM,hC,hpY,hmY,Or.inl ⟨htwo,hpos⟩,hct,hnt⟩
  rcases hpos with h0 | h1
  · exact Or.inr ⟨g,hP,hlargeY,hM,hC,hpY,hmY,Or.inr ⟨hfour,h0⟩,hct,hnt⟩
  obtain ⟨k,hk⟩ := common_four_maximal Y hP hpY h1 hfour hmY
  refine Or.inl ⟨(g.val : Model)⁻¹*k,?_⟩
  have he := congrArg (fun A : Subgroup Model =>
    A.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom) (hnt.symm.trans hk)
  rwa [map_conj_mul,map_conj_mul,inv_mul_cancel,map_conj_one] at he

/-- The common-image source branch for an arbitrary original radical whose
whole normalizer is controlled by this elementary witness. No center-size
bound is imposed, and all restriction and denominator maps are literal. -/
theorem common_four_radical (P X : Subgroup Model) (hP : P.IsPRadical 2)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ g : Model, let L := sourceSubgroup.map (MulAut.conj g).toMonoidHom
      IsTwoLocal L ∧ normalizer (P : Set Model) ≤ L ∧ P ≤ L ∧
      (normalizer (P.subgroupOf L : Set L)).map L.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf L).IsPRadical 2 ∧
      (normalizer (P.subgroupOf L : Set L)).pCoreIn 2 = P.subgroupOf L ∧
      ((normalizer (P.subgroupOf L : Set L)).pCoreIn 2).map L.subtype = P := by
  obtain ⟨g,hg⟩ := common_four_normalizer_placement X hpair hpure hpos hfour
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
