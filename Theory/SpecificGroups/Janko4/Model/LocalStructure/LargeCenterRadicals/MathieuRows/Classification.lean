module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.SharpImage
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.Cyclic
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.SmallImages.Native

/-!
# Every large-center radical in the native Mathieu local

The actual quotient image is elementary. If it is nontrivial, it cannot have
order two: both involution centralizers force a larger normal two-subgroup.
The certified common-fixed-space argument then places the entire image in
an octad kernel. Radical saturation makes it the full kernel, giving A₈.
The trivial image gives M₂₄. The quotient is always by the full intrinsic
two-core of the full ambient normalizer, including conjugate placements.

Source: An--O'Brien--Wilson (2003), §4 and Table 1, pp.122,124.
-/
public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
open ElementaryNormalizerCover MathieuHallActors SylowCore SylowCore.Transport
open Cardinality Cardinality.QuotientCount.Image
open Sporadic.Mathieu M24LocalGeometry MathieuCode
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.localKernel Cardinality.max1Subgroup

/-- A noncyclic elementary image of a kernel-containing two-group with large
center fixes a literal octad after the same native local conjugation. -/
theorem local_large_center_image_octad (U : Subgroup max1) (hp : IsPGroup 2 U)
    (hE : kernel ≤ U) [IsElementaryAbelian 2 (U.map projection)]
    (hcard : 4 ≤ Nat.card (U.map projection)) (hlarge : 64 ≤ Nat.card (center U)) :
    ∃ (g : max1) (O : Octad),
      (U.map projection).map (MulAut.conj (projection g)).toMonoidHom ≤ octadPointwiseKernel O := by
  obtain ⟨g,B,hm,hc⟩ := local_center_image_alignment U hp hE
  let m := LinearFive.Geometry.SharpImages.markedSylow
  have hmi : Function.Injective m :=
    starGroupEquivM24.injective.comp
      Simplicity.Max1Fusion.QuotientInvolutions.sylowCandidate.subtype_injective
  have helem : IsElementaryAbelian 2 (B.map m) := by
    rw [show B.map m = _ from hm]
    exact IsElementaryAbelian.map _
  let := helem
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective
    (m.subgroupMap B) (fun x y h => Subtype.ext (hmi (congrArg Subtype.val h)))
  have hb : 4 ≤ Nat.card B := by
    rw [← card_map_of_injective hmi,hm,card_map_of_injective (MulAut.conj (projection g)).injective]
    exact hcard
  obtain ⟨O,hO⟩ := SmallImages.elementary_large_fixed_octad B hb (hlarge.trans hc)
  exact ⟨g,O,hm ▸ hO⟩

/-- Every large-center radical whose whole normalizer is in max1 has the
literal full-core quotient M₂₄ or A₈. -/
theorem radical_quotient (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ max1) (hlarge : 64 ≤ Nat.card (center P)) :
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃* M24) ∨
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      alternatingGroup (Fin 8)) := by
  let U := P.subgroupOf max1
  let A := U.map projection
  have hPM := P.le_normalizer.trans hN
  let : IsElementaryAbelian 2 A := (radical_mathieu_image_small P hP hN hlarge).1
  by_cases hne : A = ⊥
  · left
    have he := radical_eq_preimage P hP hN
    change P = preimage A at he
    rw [hne,preimage_bot] at he
    rw [he]
    exact ⟨kernelNormalizerQuotientEquiv⟩
  have hA : A.IsPRadical 2 := ⟨hne,radical_image_core P hP hN⟩
  have hfour : 4 ≤ Nat.card A := by
    obtain ⟨n,hn⟩ := hA.isPGroup.exists_card_eq
    have hn2 : 2 ≤ n := by
      by_contra hnlt
      have hnlt' : n < 2 := by omega
      interval_cases n
      · exact hne (card_eq_one.mp (by simpa using hn))
      · exact radical_image_card_ne_two A hA (by simpa using hn)
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn2
  have hE : kernel ≤ U := by
    intro x hx
    exact kernel_le_radical P hP hN (mem_map_of_mem max1.subtype hx)
  have hc : 64 ≤ Nat.card (center U) := by
    rw [Nat.card_congr (centerCongr (subgroupOfEquivOfLe hPM)).toEquiv]
    exact hlarge
  obtain ⟨g,O,hg⟩ := local_large_center_image_octad U
    (hP.isPGroup.comap_of_injective max1.subtype max1.subtype_injective) hE hfour hc
  let c := MulAut.conj (projection g)
  have he : A.map c.toMonoidHom = octadPointwiseKernel O :=
    radical_eq_octad_kernel _ (hA.map_equiv c) O hg
  have hn : (normalizer (A : Set M24)).map c.toMonoidHom = octadStabilizer O := by
    rw [map_equiv_normalizer_eq,he,octad_kernel_normalizer]
  let e : normalizer (A : Set M24) ≃* octadStabilizer O :=
    (c.subgroupMap _).trans (MulEquiv.subgroupCongr hn)
  exact Or.inr ⟨(radicalNormalizerQuotientEquiv P hP hN).trans
    ((coreQuotientCongr e).trans
      ((M24ChapterHStabilizers.OctadAction.quotientEquiv O).trans
        Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8))⟩

/-- Conjugate placements retain the quotient of the original whole normalizer. -/
theorem radical_quotient_of_conjugate (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hlarge : 64 ≤ Nat.card (center P)) (g : Model)
    (hN : normalizer (P : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom) :
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃* M24) ∨
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      alternatingGroup (Fin 8)) := by
  let c := (MulAut.conj g).symm
  let Q := P.map c.toMonoidHom
  let a : normalizer (P : Set Model) ≃* normalizer (Q : Set Model) :=
    (c.subgroupMap _).trans (MulEquiv.subgroupCongr (map_equiv_normalizer_eq P c))
  have hQ := hP.map_equiv c
  have hlargeQ : 64 ≤ Nat.card (center Q) :=
    hlarge.trans_eq (Nat.card_congr (centerCongr (c.subgroupMap P)).toEquiv)
  have hQc : normalizer (Q : Set Model) ≤ max1 := by
    rw [← map_equiv_normalizer_eq P c]
    have hh := map_mono (f := c.toMonoidHom) hN
    have hi : c.toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id Model := by
      ext x
      exact (MulAut.conj g).symm_apply_apply x
    simpa only [map_map,hi,map_id] using hh
  rcases radical_quotient Q hQ hQc hlargeQ with h | h
  · obtain ⟨e⟩ := h
    exact Or.inl ⟨(coreQuotientCongr a).trans e⟩
  · obtain ⟨e⟩ := h
    exact Or.inr ⟨(coreQuotientCongr a).trans e⟩

end Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
