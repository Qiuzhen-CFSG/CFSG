module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.TriangleGeneration
public import Theory.SpecificGroups.AlternatingFiveCentralTwoProduct

/-!
# The actual third parabolic has the A₅ × C₂ model

The literal join has order 120 and meets the full involution core in the
original involution line. Restricting the original local quotient gives a
surjection onto A₅ with that full central kernel of order two. A noncentral
involution in the original A₄ × C₂ point intersection lies outside the
kernel, so the central cover splits. No triangle model or complement is
assumed in the original source context.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Janko23.J3Recognition.Ambient.Seventeen
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

variable {G : Type*} [Group G] [Finite G]

set_option maxHeartbeats 800000 in
/-- Baumeister's literal third parabolic, constructed from the same field
embedding, is the genuine A₅ × C₂ group. -/
theorem literal_triangle_equiv
    {D : Seed G} (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : SingerField.Model →* G)
    (hj : PlaneTransport.FieldEmbedding A C a j) :
    Nonempty (third j.range (overlap j) (j SingerField.fieldElement) ≃* Sporadic.Janko3.SourceRecognition.Seventeen.TriangleGroup) := by
  let f := j SingerField.fieldElement
  let H := Janko23.involutionCentralizer f
  let Q := Janko23.localCore f
  let R := third j.range (overlap j) f
  let X := j.range ⊓ H
  have hf : orderOf f = 2 := image_involution_order j hj.1
  obtain ⟨hRH,hQR,_hgen,hR⟩ := literal_triangle_generation P hc A C a j hj
  obtain ⟨_,_,⟨eA⟩⟩ := literal_involution_core_and_quotient (D := D) hc f hf
  let r : R →* alternatingGroup (Fin 5) :=
    eA.toMonoidHom.comp ((QuotientGroup.mk' Q).comp (inclusion hRH))
  have hk : r.ker = (zpowers f).subgroupOf R := by
    ext x
    change eA (QuotientGroup.mk' Q (inclusion hRH x)) = 1 ↔ (x : G) ∈ zpowers f
    rw [eA.map_eq_one_iff]
    change (QuotientGroup.mk (inclusion hRH x) : H ⧸ Q) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    change inclusion hRH x ∈ Janko23.localCore f ↔ _
    rw [←Janko23.ambientCore_subgroupOf]
    change (x : G) ∈ Janko23.ambientCore f ↔ (x : G) ∈ zpowers f
    exact ⟨fun hx => hQR ▸ ⟨hx,x.property⟩,fun hx => (hQR.symm ▸ hx).1⟩
  have hZR : zpowers f ≤ R := hQR ▸ inf_le_right
  have hkc : Nat.card r.ker = 2 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe hZR).toEquiv,Nat.card_zpowers,hf]
  have hrange : Nat.card r.range = 60 := by
    have hh := r.ker.index_mul_card
    rw [index_ker,hkc,hR] at hh
    omega
  have hr : Function.Surjective r := by
    apply MonoidHom.range_eq_top.mp
    apply eq_top_of_card_eq
    rw [hrange,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  let fR : R := ⟨f,hZR (mem_zpowers f)⟩
  have hfcenter : fR ∈ center R := mem_center_iff.mpr fun x =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (hRH x.property))
  have hkline : r.ker = zpowers fR := by
    apply map_injective R.subtype_injective
    rw [hk,subgroupOf_map_subtype,inf_eq_left.mpr hZR,MonoidHom.map_zpowers]
    rfl
  have hkcenter : r.ker ≤ center R := hkline ▸ zpowers_le.mpr hfcenter
  let eX : X ≃* (alternatingGroup (Fin 4) × Multiplicative (ZMod 2)) :=
    PointCentralizer.imagePointCentralizerEquiv j hj.1
  have hm : ∃ u : alternatingGroup (Fin 4) × Multiplicative (ZMod 2),
      u^2=1 ∧ u ∉ center (alternatingGroup (Fin 4) × Multiplicative (ZMod 2)) := by
    decide +kernel
  obtain ⟨u,hu,huc⟩ := hm
  let x := eX.symm u
  have hx2 : x^2=1 := eX.injective (by rw [map_pow,eX.apply_symm_apply,hu,map_one])
  have hXR : X ≤ R := le_sup_left
  let xR : R := inclusion hXR x
  have hxR2 : xR^2=1 := by rw [←map_pow,hx2,map_one]
  have hxr : r xR ≠ 1 := by
    intro hz
    have hxc : xR ∈ center R := hkcenter hz
    have hxcX : x ∈ center X := by
      apply mem_center_iff.mpr
      intro z
      apply Subtype.ext
      exact congrArg (fun t : R => (t : G)) (mem_center_iff.mp hxc (inclusion hXR z))
    apply huc
    apply mem_center_iff.mpr
    intro v
    obtain ⟨z,rfl⟩ := eX.surjective v
    simpa only [map_mul,x,eX.apply_symm_apply] using congrArg eX (mem_center_iff.mp hxcX z)
  exact alternatingGroup.central_two_product_of_involution r hr hkcenter hkc xR hxR2 hxr

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
