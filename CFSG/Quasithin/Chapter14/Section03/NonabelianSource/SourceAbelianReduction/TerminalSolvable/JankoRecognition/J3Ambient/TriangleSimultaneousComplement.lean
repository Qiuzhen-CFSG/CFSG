module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.TrianglePointCoordinates
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.TrianglePairGenerators
public import Theory.GroupTheory.QuotientKernelComplement

/-!
# One actual complement retaining both parabolic intersections

The original point section is already marked as the standard A₄ in the
central quotient. The literal pair subgroup has a genuine involution
inverting their common cubic. Its affine translation is corrected by a
vector fixed by the entire point stabilizer. The same conjugated complement
therefore contains both original sections, and its full central preimage
retains the literal involution line and the full involution core.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
open BinaryPermutation.AlternatingFiveExtension
open BinaryPermutation.AlternatingFiveBorel

private theorem affine_complement :
    (SemidirectProduct.inl : V →* TriangleTranslation.Model).range.IsComplement'
      (SemidirectProduct.inr : alternatingGroup (Fin 5) →* TriangleTranslation.Model).range := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · apply disjoint_def.mpr
    rintro x ⟨v,rfl⟩ ⟨g,hg⟩
    have hv := congrArg SemidirectProduct.left hg
    change 1 = v at hv
    rw [←hv,map_one]
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    exact ⟨SemidirectProduct.inl x.left,⟨x.left,rfl⟩,
      SemidirectProduct.inr x.right,⟨x.right,rfl⟩,
      SemidirectProduct.inl_left_mul_inr_right x⟩

variable {G : Type*} [Group G] [Finite G]

set_option maxHeartbeats 800000 in
/-- The same actual order-120 central preimage contains both original
parabolic intersections, meeting the full involution core in the literal involution line. -/
theorem literal_triangle_simultaneous_complement
    {D : Seed G} (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : SingerField.Model →* G)
    (hj : PlaneTransport.FieldEmbedding A C a j) :
    let f := j SingerField.fieldElement
    let H := Janko23.involutionCentralizer f
    let X := j.range ⊓ H
    let Y := normalizer (overlap j : Set G) ⊓ H
    ∃ R : Subgroup G, R ≤ H ∧ X ≤ R ∧ Y ≤ R ∧
      Janko23.ambientCore f ⊓ R = zpowers f ∧
      Janko23.ambientCore f ⊔ R = H ∧ Nat.card R = 120 := by
  let f := j SingerField.fieldElement
  let s := j cubic
  let H := Janko23.involutionCentralizer f
  let Q := Janko23.localCore f
  let X := j.range ⊓ H
  let Y := normalizer (overlap j : Set G) ⊓ H
  let q := QuotientGroup.mk' (center H)
  obtain ⟨E,hEcore,hEX⟩ := literal_triangle_point_coordinates P hc A C a j hj
  let : Finite TriangleTranslation.Model := Finite.of_injective E.symm E.symm.injective
  obtain ⟨hZmap,hZ,_hV,_hU,_hd,_hi,_hK⟩ := literal_triangle_quotient_splitting P hc A C a j hj
  obtain ⟨y,hyY,hy2,hys,hYgen⟩ := literal_triangle_pair_generators P hc A C a j hj
  let φ : H →* TriangleTranslation.Model := E.toMonoidHom.comp q
  have hφker : φ.ker = center H := by
    rw [MonoidHom.ker_comp_of_injective _ _ E.injective,QuotientGroup.ker_mk']
  have hsH : s ∈ H := mem_centralizer_singleton_iff.mpr
    ((cubic_commutes_complement
      ⟨SingerField.fieldElement,(mem_pointComplement _).mpr rfl⟩).map j).eq
  have hsX : s ∈ X := ⟨⟨cubic,rfl⟩,hsH⟩
  let sH : H := ⟨s,hsH⟩
  let yH : H := ⟨y,hyY.2⟩
  have hsimage : φ sH ∈ B.map
      (SemidirectProduct.inr : alternatingGroup (Fin 5) →* TriangleTranslation.Model) := by
    rw [←hEX]
    exact mem_map_of_mem E.toMonoidHom (mem_map_of_mem q hsX)
  obtain ⟨sA,hsB,hsA⟩ := hsimage
  have hsorder : orderOf sH = 3 :=
    (orderOf_coe sH).symm.trans ((orderOf_injective j hj.1 _).trans cubic_order)
  have hsφne : φ sH ≠ 1 := by
    intro hh
    have hsZ : sH ∈ center H := hφker ▸ hh
    have hd := _root_.orderOf_dvd_natCard (x := (⟨sH,hsZ⟩ : center H))
    rw [←orderOf_coe,hsorder,hZ] at hd
    norm_num at hd
  have hsAorder : orderOf sA = 3 := by
    have hi : orderOf (φ sH) = 3 := orderOf_eq_prime (by
      rw [←map_pow,←hsorder,pow_orderOf_eq_one,map_one]) hsφne
    rw [←hsA,orderOf_injective _ SemidirectProduct.inr_injective] at hi
    exact hi
  have hyφ : φ yH ^ 2 = 1 := by
    rw [←map_pow,show yH^2=1 from Subtype.ext hy2,map_one]
  have hiφ : φ yH * SemidirectProduct.inr sA * (φ yH)⁻¹ = SemidirectProduct.inr sA⁻¹ := by
    rw [hsA,←map_inv,←map_mul,←map_mul]
    have hh : yH*sH*yH⁻¹=sH⁻¹ := Subtype.ext hys
    rw [hh,map_inv,←hsA,map_inv]
  obtain ⟨b,hb,hby,hbmem⟩ := TriangleTranslation.inverter_translation sA hsAorder hsB (φ yH) hyφ hiφ
  let N := (SemidirectProduct.inl : V →* TriangleTranslation.Model).range
  let K := (SemidirectProduct.inr : alternatingGroup (Fin 5) →* TriangleTranslation.Model).range
  let c := MulAut.conj (SemidirectProduct.inl b : TriangleTranslation.Model)
  let L := K.map c.toMonoidHom
  have hNL : N.IsComplement' L := by
    apply isComplement'_of_card_mul_and_disjoint
    · rw [card_map_of_injective c.injective]
      exact affine_complement.card_mul_card
    · have hh := disjoint_map (f := c.toMonoidHom) c.injective affine_complement.disjoint
      have hn : N.map c.toMonoidHom = N := by
        rw [show N = (SemidirectProduct.rightHom : TriangleTranslation.Model →* alternatingGroup (Fin 5)).ker
          from SemidirectProduct.range_inl_eq_ker_rightHom]
        exact Subgroup.Normal.map_conj_eq _ _
      rwa [hn] at hh
  have hXL (x : H) (hx : (x : G) ∈ X) : φ x ∈ L := by
    have hximage : φ x ∈ B.map
        (SemidirectProduct.inr : alternatingGroup (Fin 5) →* TriangleTranslation.Model) := by
      rw [←hEX]
      exact mem_map_of_mem E.toMonoidHom (mem_map_of_mem q hx)
    obtain ⟨g,hg,hgx⟩ := hximage
    refine ⟨SemidirectProduct.inr g,⟨g,rfl⟩,?_⟩
    change SemidirectProduct.inl b * SemidirectProduct.inr g *
      (SemidirectProduct.inl b : TriangleTranslation.Model)⁻¹ = φ x
    rw [(hb g hg).eq,mul_inv_cancel_right]
    exact hgx
  let K' := L.comap E.toMonoidHom
  have hK' : (Q.map q).IsComplement' K' := by
    apply QuotientKernelComplement.complement_comap E.toMonoidHom (Q.map q) L
    · rw [E.toMonoidHom.ker_eq_bot E.injective]
      exact disjoint_bot_right
    · rw [hEcore]
      exact hNL
  obtain ⟨R,hR,hZR,hQR,hgen,r,hr,hker,_hrep⟩ :=
    exists_preimage_of_quotient_complement Q (center H) Janko23.HTypeAt.center_le_core K' hK'
  have hXR : X ≤ R.map H.subtype := by
    intro x hx
    refine ⟨⟨x,hx.2⟩,?_,rfl⟩
    rw [hR]
    exact hXL ⟨x,hx.2⟩ hx
  have hyR : y ∈ R.map H.subtype := by
    refine ⟨yH,?_,rfl⟩
    rw [hR]
    exact hbmem
  have hfR : f ∈ R.map H.subtype := by
    have hh : zpowers f ≤ R.map H.subtype := hZmap ▸ map_mono hZR
    exact hh (mem_zpowers f)
  have hYR : Y ≤ R.map H.subtype := by
    change Y = (zpowers f ⊔ zpowers s) ⊔ zpowers y at hYgen
    rw [hYgen]
    exact sup_le (sup_le (zpowers_le.mpr hfR) (zpowers_le.mpr (hXR hsX))) (zpowers_le.mpr hyR)
  have hcard : Nat.card R = 120 := by
    obtain ⟨_,_,⟨eA⟩⟩ := literal_involution_core_and_quotient (D := D) hc f (image_involution_order j hj.1)
    have hk : Nat.card r.ker = 2 := by
      rw [hker,Nat.card_congr (subgroupOfEquivOfLe hZR).toEquiv,hZ]
    have hh := r.ker.index_mul_card
    rw [index_ker,MonoidHom.range_eq_top.mpr hr,
      Nat.card_congr (topEquiv (G := H ⧸ Q)).toEquiv,
      Nat.card_congr eA.toEquiv,nat_card_alternatingGroup,hk] at hh
    norm_num at hh
    exact hh.symm
  refine ⟨R.map H.subtype,map_subtype_le _,hXR,hYR,?_,?_,?_⟩
  · have hh := congrArg (Subgroup.map H.subtype) hQR
    rw [map_inf _ _ _ H.subtype_injective,hZmap] at hh
    exact hh
  · have hh := congrArg (Subgroup.map H.subtype) hgen
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  · rw [card_map_of_injective H.subtype_injective,hcard]

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
