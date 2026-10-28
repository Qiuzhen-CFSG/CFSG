module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularImages.ExactRows

/-!
# Exact nonsingular row selection through the original ambient quotient

The finite subspace refinement replaces container inclusion by exact whole-row
identification outside Figure 2(a). The same seed-centralizer lift preserves
both markings and transports the full centralizer and normalizer. Its image
identity is proved in both directions through the original `starHom`.

This is the literal positioned-source application of KW Lemma 2.3.1. Initial
positioning and the remaining pure-2A and nonsingular geometry are still needed
for the exhaustive four-local cover.
Source: Kleidman--Wilson (1988), Lemma 2.3.1, printed p.492.
-/

set_option backward.isDefEq.respectTransparency true
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages
open Cardinality.QuotientCount.Image ElementaryEightGeometry InvolutionCentralizers.Second
open scoped Pointwise IsMulCommutative
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel

/-- Outside a conjugate of the box image, the original seed and pair select
one of five exact literal images. The lifted conjugator preserves both markings
and transports the whole centralizer and normalizer by the same ambient map. -/
theorem source_exact_row_positioning (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hp : pairPermutation ∈ (X.subgroupOf Local).map starHom) :
    ∃ g : localCentralizer,
      starHom g.val ∈ pairCentralizer ∧
      let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
      Y ≤ Local ∧ (seed : Model) ∈ Y ∧
      pairPermutation ∈ (Y.subgroupOf Local).map starHom ∧
      ((Y.subgroupOf Local).map starHom ≤ boxImage ∨
        ∃ k : Fin 5, (Y.subgroupOf Local).map starHom = Refinement.exactRow k) ∧
      centralizer (Y : Set Model) = (centralizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)⁻¹).toMonoidHom ∧
      normalizer (Y : Set Model) = (normalizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)⁻¹).toMonoidHom := by
  have hXL : X ≤ Local := X.le_centralizer.trans
    ((centralizer_le (Set.singleton_subset_iff.mpr hs)).trans ambient_le_max1)
  let A := (X.subgroupOf Local).map starHom
  let : IsElementaryAbelian 2 (X.subgroupOf Local) := IsElementaryAbelian.subgroupOf hXL
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map starHom
  obtain ⟨u,hu⟩ := Refinement.elementary_container_exact_rows A (source_image_le_container X hs hp) hp
  obtain ⟨g,hg⟩ := toStarPair_surjective (⟨u.val,u.property.2⟩ : starPairStabilizer)
  have hg' : starHom g.val = u.val := congrArg Subtype.val hg
  let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
  have hYL : Y ≤ Local := by
    rintro y ⟨x,hx,rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      Local.mul_mem (Local.mul_mem (Local.inv_mem g.val.property) (hXL hx)) g.val.property
  have hseed : (MulAut.conj (g.val : Model)⁻¹) seed = (seed : Model) := by
    have hc := congrArg (fun x : Local => (x : Model))
      (mem_centralizer_singleton_iff.mp g.property)
    change (g.val : Model) * (seed : Model) = (seed : Model) * g.val at hc
    change (g.val : Model)⁻¹ * seed * ((g.val : Model)⁻¹)⁻¹ = (seed : Model)
    rw [inv_inv,mul_assoc,← hc,inv_mul_cancel_left]
  have image_forward (x : Local) (hx : (x : Model) ∈ X) :
      starHom (g.val⁻¹ * x * g.val) ∈ (Y.subgroupOf Local).map starHom := by
    apply mem_map_of_mem starHom
    exact mem_map.mpr ⟨x,hx,by simp [mul_assoc]⟩
  refine ⟨g,hg' ▸ u.property.1,hYL,?_,?_,?_,?_,?_⟩
  · rw [← hseed]
    exact mem_map_of_mem (MulAut.conj (g.val : Model)⁻¹).toMonoidHom hs
  · obtain ⟨x,hx,hxp⟩ := hp
    have h := image_forward x hx
    have he : starHom (g.val⁻¹ * x * g.val) = pairPermutation := by
      rw [map_mul,map_mul,map_inv,hg',hxp]
      have hc := mem_centralizer_singleton_iff.mp u.property.1
      rw [mul_assoc,← hc,inv_mul_cancel_left]
    exact he ▸ h
  · have himage : (Y.subgroupOf Local).map starHom =
        A.map (MulAut.conj (u : StarGroup)⁻¹).toMonoidHom := by
      apply le_antisymm
      · rintro p ⟨y,hy,rfl⟩
        obtain ⟨x,hx,he⟩ := hy
        let x0 : Local := ⟨x,hXL hx⟩
        have hye : y = g.val⁻¹ * x0 * g.val := by
          apply Subtype.ext
          simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
            coe_mul, coe_inv, subtype_apply, x0] using he.symm
        refine ⟨starHom x0,mem_map_of_mem starHom (show x0 ∈ X.subgroupOf Local from hx),?_⟩
        rw [hye,map_mul,map_mul,map_inv,hg']
        simp [hg']
      · rintro p ⟨v,⟨x,hx,hxv⟩,rfl⟩
        have h := image_forward x hx
        rw [map_mul,map_mul,map_inv,hg',hxv] at h
        simpa using h
    rw [himage]
    rcases hu with h | ⟨k,h⟩
    · left
      rintro p ⟨v,hv,rfl⟩
      obtain ⟨z,hz,hzv⟩ := h hv
      rw [← hzv]
      simpa [mul_assoc] using hz
    · right
      refine ⟨k,?_⟩
      rw [h,map_map]
      have he : (MulAut.conj (u : StarGroup)⁻¹).toMonoidHom.comp
          (MulAut.conj (u : StarGroup)).toMonoidHom = MonoidHom.id _ := by
        ext x
        simp [mul_assoc]
      rw [he,map_id]

  · exact (map_centralizer_equiv (X : Set Model) (MulAut.conj (g.val : Model)⁻¹)).symm
  · exact (map_equiv_normalizer_eq X (MulAut.conj (g.val : Model)⁻¹)).symm


end Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages
