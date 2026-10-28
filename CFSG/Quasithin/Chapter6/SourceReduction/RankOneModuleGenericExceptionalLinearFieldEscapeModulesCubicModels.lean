module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.PSL3FourExclusion
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Restriction

/-!
# The two source cubic models for the literal PSL₃(4) component

At cubic ratio at most two, the completed linear module sieve gives a
natural module or the half-field tensor. Faithfulness excludes the natural
row because SL₃(4) has a cubic center and PSL₃(4) is centerless. The tensor
has half-degree one. Its actual cover and descended intertwiner therefore
identify the original action with the nine-dimensional Hermitian action.
An existing diagram obstruction excludes that remaining row.

This is the B.4/K.3 step in Aschbacher--Smith 5.1.23, printed p.646,
`refs/quasithin.pdf`. Irreducibility on the component is explicit here;
the orbit application must establish it before using this bound.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
open ChapterK.Linear.Recognition ChapterB.QuasisimpleSource
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
universe u v
variable {X : Type u} [Group X] [Finite X]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

theorem hermitian_coordinates_of_small_cubic
    (ρ : Representation (ZMod 2) X W) (K : Subgroup X)
    (κ : GroupClass.{u}) (hsq : IsSQTK κ X)
    (hfit : generalizedFitting X = K) (hm : ClassicalGroup.IsPSL K 3 4)
    (hf : Function.Injective ρ) (hi : Representation.IsIrreducible (ρ.comp K.subtype))
    (hq : cubicRatio ρ ≤ 2) :
    ∃ (j : K ≃* PSL(3,E 1)) (c : W ≃ₗ[ZMod 2] Space 1),
      ∀ k : K, ∀ w, c (ρ k w) = projectiveAction (j k) (c w) := by
  obtain ⟨hqs,hz,hquot⟩ := PSL3FourExclusion.model_facts hm
  have h : SourceHypothesis κ ρ K :=
    ⟨inferInstance,inferInstance,hsq,hfit,hqs,hf,hi,hq⟩
  obtain ⟨B,hB,eQ,C,_⟩ := SourceFF.exists_binaryField_cover h 2 (by decide) hquot
  let := inflated_irreducible ρ C hi
  obtain ⟨hs,hn | ht⟩ := SourceFF.absolute_models h C eQ
  · obtain ⟨hN⟩ := SourceFF.naturalSourceInput_of_absolute h C hn.1 hn.2.2
    have hc := Nat.card_congr (centerCongr hN.natural.groupEquiv).toEquiv
    change Nat.card (center K) = Nat.card (center SL(3,B.Carrier)) at hc
    rw [hz,Atlas.ExceptionalSupport.card_sl_center,B.card_eq,hB] at hc
    norm_num at hc
  · have hd : schurDegree (inflated ρ C) = 1 := by omega
    obtain ⟨a,⟨e⟩⟩ := TwistedExclusion.exists_binary_hermitian_equiv 1 (inflated ρ C)
      (by rw [B.card_eq,hB]) hd (by simpa only [hd] using ht.2.2)
    let π := C.projection.comp a.toMonoidHom
    have hπ : Function.Surjective π := C.surjective.comp a.surjective
    let d := hermitianActionEquiv (ρ.comp K.subtype) 1 π hπ
      (hf.comp K.subtype_injective) e
    let j := d.groupEquiv.trans ((binaryImageEquiv 1).symm.trans (imageEquivPSL 1 (by decide)))
    refine ⟨j,d.linearEquiv,?_⟩
    intro k w
    have he := d.intertwines k w
    change d.linearEquiv (ρ k w) = (d.groupEquiv k).val (d.linearEquiv w) at he
    rw [he]
    change _ = ((binaryImageEquiv 1) ((imageEquivPSL 1 (by decide)).symm
      ((imageEquivPSL 1 (by decide)) ((binaryImageEquiv 1).symm (d.groupEquiv k))))).val _
    rw [MulEquiv.symm_apply_apply,MulEquiv.apply_symm_apply]

/-- With the Hermitian row excluded, the same irreducible component action
has cubic ratio strictly greater than two. -/
theorem cubicRatio_gt_two_of_no_hermitian
    (ρ : Representation (ZMod 2) X W) (K : Subgroup X)
    (κ : GroupClass.{u}) (hsq : IsSQTK κ X)
    (hfit : generalizedFitting X = K) (hm : ClassicalGroup.IsPSL K 3 4)
    (hf : Function.Injective ρ) (hi : Representation.IsIrreducible (ρ.comp K.subtype))
    (hd : ¬ ∃ (j : K ≃* PSL(3,E 1)) (c : W ≃ₗ[ZMod 2] Space 1),
      ∀ k : K, ∀ w, c (ρ k w) = projectiveAction (j k) (c w)) :
    2 < cubicRatio ρ := by
  exact lt_of_not_ge (fun hq => hd
    (hermitian_coordinates_of_small_cubic ρ K κ hsq hfit hm hf hi hq))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
