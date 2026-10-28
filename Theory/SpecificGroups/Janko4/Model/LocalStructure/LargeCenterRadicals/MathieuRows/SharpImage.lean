module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.CenterBounds
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.OctadSaturation
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.SharpImages.Native

/-!
# The order-sixteen Mathieu image of a large-center radical

The sharp native fixed-mask bound identifies the full pointwise octad kernel
whenever the elementary image order times the lifted center order is at least
1024. The lift need only be a two-group containing the binary kernel; it need
not be elementary. Sylow alignment retains the actual local conjugator and
the original Mathieu projection.

For a radical whose whole normalizer lies in max1, image order sixteen and
center order at least 64 therefore give the full intrinsic A₈ quotient.
Together with the trivial-image M₂₄ row, the remaining arbitrary-radical
problem has elementary radical images of orders two, four or eight.

Source: An--O'Brien--Wilson (2003), Section 4 and Table 1, pp.122,124;
the sharp native action calculation used for Kleidman--Wilson (1988),
Lemma 1.1.2(ii), p.485.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
open ElementaryNormalizerCover MathieuHallActors SylowCore SylowCore.Transport
open Cardinality Cardinality.QuotientCount.Image
open Sporadic.Mathieu M24LocalGeometry MathieuCode
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.localKernel Cardinality.max1Subgroup

private theorem projection_star (g : max1) :
    projection g = starGroupEquivM24 (starProjection matrixA_mul_self matrixB_pow_four g) := by
  have he : projection = starGroupEquivM24.toMonoidHom.comp
      (starProjection matrixA_mul_self matrixB_pow_four) := by
    apply MonoidHom.eq_of_eqOn_dense (localXY_generate matrixA_mul_self matrixB_pow_four)
    intro x hx
    rcases (show x = localX matrixA_mul_self matrixB_pow_four ∨
        x = localY matrixA_mul_self matrixB_pow_four from hx) with rfl | rfl
    · change localQuotientEquivM24 matrixA_mul_self matrixB_pow_four
        (QuotientGroup.mk' _ _) = starGroupEquivM24 _
      rw [localQuotientEquivM24_apply, starProjection_x]
      congr 1
      apply Subtype.ext
      exact actionImageEquivStarGroup_x matrixA_mul_self matrixB_pow_four
    · change localQuotientEquivM24 matrixA_mul_self matrixB_pow_four
        (QuotientGroup.mk' _ _) = starGroupEquivM24 _
      rw [localQuotientEquivM24_apply, starProjection_y]
      congr 1
      apply Subtype.ext
      exact actionImageEquivStarGroup_y matrixA_mul_self matrixB_pow_four
  exact DFunLike.congr_fun he g

private theorem image_conjugate (U : Subgroup max1) (g : max1) :
    (U.map (MulAut.conj g).toMonoidHom).map projection =
      (U.map projection).map (MulAut.conj (projection g)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulAut.conj_apply, map_mul, map_inv]

/-- Align the actual image and its full center with the certified star Sylow,
retaining the same local conjugator and the literal Mathieu projection. -/
theorem local_center_image_alignment (U : Subgroup max1) (hp : IsPGroup 2 U)
    (hE : kernel ≤ U) :
    ∃ (g : max1) (B : Subgroup Simplicity.Max1Fusion.QuotientInvolutions.sylowCandidate),
      B.map LinearFive.Geometry.SharpImages.markedSylow =
        (U.map projection).map (MulAut.conj (projection g)).toMonoidHom ∧
      Nat.card (center U) ≤ Nat.card (FixedMasks B) := by
  obtain ⟨S,hUS⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := exists_alignment S
  let A := U.subgroupOf S.toSubgroup
  let f := alignedHom S g hg
  let B := A.map f
  let m := LinearFive.Geometry.SharpImages.markedSylow
  have hm : B.map m = (U.map projection).map (MulAut.conj (projection g)).toMonoidHom := by
    change (A.map f).map m = _
    rw [map_map]
    have he : m.comp f = (projection.comp (MulAut.conj g).toMonoidHom).comp
        S.toSubgroup.subtype := by
      apply MonoidHom.ext
      intro x
      exact (projection_star ((MulAut.conj g) x.val)).symm
    rw [he, ← map_map, map_subgroupOf_eq_of_le hUS]
    rw [← map_map]
    exact image_conjugate U g
  have hzE (z : center U) : z.val.val ∈ kernel := by
    change z.val.val ∈ Cardinality.localKernel matrixA_mul_self matrixB_pow_four
    rw [← centralizer_localKernel matrixA_mul_self matrixB_pow_four]
    intro v hv
    exact congrArg U.subtype (mem_center_iff.mp z.property ⟨v,hE hv⟩)
  let j : center U → (centralizer (A : Set S)).subgroupOf (core S) := fun z =>
    ⟨⟨⟨z.val.val,hUS z.val.property⟩,hzE z⟩,by
      intro a ha
      apply Subtype.ext
      exact congrArg U.subtype (mem_center_iff.mp z.property ⟨a.val,ha⟩)⟩
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val.val.val) h))
  have hc : Nat.card (center U) ≤ Nat.card (FixedMasks B) :=
    (Nat.card_le_card_of_injective j hj).trans (centralizer_card_le_fixedMasks S A g hg)
  exact ⟨g,B,hm,hc⟩

/-- The sharp fixed-mask bound applies to the full center of a two-group
containing the native kernel; the lifted group need not be elementary. -/
theorem local_sharp_center_image_octad (U : Subgroup max1) (hp : IsPGroup 2 U)
    (hE : kernel ≤ U) [IsElementaryAbelian 2 (U.map projection)]
    (hne : U.map projection ≠ ⊥)
    (hlarge : 1024 ≤ Nat.card (U.map projection) * Nat.card (center U)) :
    ∃ g : max1, (U.map projection).map (MulAut.conj (projection g)).toMonoidHom =
      octadPointwiseKernel LinearFive.Geometry.SharpImages.exceptionalOctad := by
  obtain ⟨g,B,hm,hc⟩ := local_center_image_alignment U hp hE
  let m := LinearFive.Geometry.SharpImages.markedSylow
  have hmi : Function.Injective m :=
    starGroupEquivM24.injective.comp
      Simplicity.Max1Fusion.QuotientInvolutions.sylowCandidate.subtype_injective
  have helem : IsElementaryAbelian 2 (B.map m) := by
    rw [hm]
    exact IsElementaryAbelian.map _
  let := helem
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective
    (m.subgroupMap B) (fun x y h => Subtype.ext (hmi (congrArg Subtype.val h)))
  have hcard : Nat.card B = Nat.card (U.map projection) := by
    rw [← card_map_of_injective hmi, hm, card_map_of_injective (MulAut.conj (projection g)).injective]
  have hB : B ≠ ⊥ := by
    intro hb
    have h0 : Nat.card (U.map projection) = 1 := by
      rw [← hcard, hb, card_bot]
    exact hne (card_eq_one.mp h0)
  refine ⟨g, hm ▸ LinearFive.Geometry.SharpImages.elementary_large_image_eq_octad B hB ?_⟩
  rw [hcard]
  exact hlarge.trans (Nat.mul_le_mul_left _ hc)

/-- An actual Mathieu image of order sixteen gives the full A₈ quotient of
its original native radical normalizer. -/
theorem radical_image_sixteen_quotient (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ max1) (hlarge : 64 ≤ Nat.card (center P))
    (hcard : Nat.card ((P.subgroupOf max1).map projection) = 16) :
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      alternatingGroup (Fin 8)) := by
  let U := P.subgroupOf max1
  let A := U.map projection
  have hPM := P.le_normalizer.trans hN
  let : IsElementaryAbelian 2 A := (radical_mathieu_image_small P hP hN hlarge).1
  have hE : kernel ≤ U := by
    intro x hx
    exact kernel_le_radical P hP hN (mem_map_of_mem max1.subtype hx)
  have hne : A ≠ ⊥ := by
    intro he
    change Nat.card A = 16 at hcard
    rw [he,card_bot] at hcard
    omega
  have hc : 64 ≤ Nat.card (center U) := by
    rw [Nat.card_congr (centerCongr (subgroupOfEquivOfLe hPM)).toEquiv]
    exact hlarge
  have hproduct : 1024 ≤ Nat.card A * Nat.card (center U) := by
    rw [show Nat.card A = 16 from hcard]
    omega
  obtain ⟨g,hg⟩ := local_sharp_center_image_octad U
    (hP.isPGroup.comap_of_injective max1.subtype max1.subtype_injective) hE hne hproduct
  let c := MulAut.conj (projection g)
  let O := LinearFive.Geometry.SharpImages.exceptionalOctad
  have hn : (normalizer (A : Set M24)).map c.toMonoidHom = octadStabilizer O := by
    rw [map_equiv_normalizer_eq, show A.map c.toMonoidHom = octadPointwiseKernel O from hg,
      octad_kernel_normalizer]
  let e : normalizer (A : Set M24) ≃* octadStabilizer O :=
    (c.subgroupMap _).trans (MulEquiv.subgroupCongr hn)
  exact ⟨(radicalNormalizerQuotientEquiv P hP hN).trans
    ((coreQuotientCongr e).trans
      ((M24ChapterHStabilizers.OctadAction.quotientEquiv O).trans
        Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8))⟩

/-- The placed arbitrary-radical quotient problem now leaves only genuine
nontrivial elementary Mathieu radical images of orders two, four or eight. -/
theorem radical_quotient_or_small_mathieu_image (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ max1) (hlarge : 64 ≤ Nat.card (center P)) :
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      M24) ∨
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      alternatingGroup (Fin 8)) ∨
    (let A := (P.subgroupOf max1).map projection;
      A.IsPRadical 2 ∧ IsElementaryAbelian 2 A ∧
        (Nat.card A = 2 ∨ Nat.card A = 4 ∨ Nat.card A = 8)) := by
  let A := (P.subgroupOf max1).map projection
  obtain ⟨helem,hbound⟩ := radical_mathieu_image_small P hP hN hlarge
  by_cases hne : A = ⊥
  · left
    have he := radical_eq_preimage P hP hN
    change P = preimage A at he
    rw [hne,preimage_bot] at he
    rw [he]
    exact ⟨kernelNormalizerQuotientEquiv⟩
  by_cases h16 : Nat.card A = 16
  · exact Or.inr (Or.inl (radical_image_sixteen_quotient P hP hN hlarge h16))
  right; right
  refine ⟨⟨hne, radical_image_core P hP hN⟩, helem, ?_⟩
  change Nat.card A = 2 ∨ Nat.card A = 4 ∨ Nat.card A = 8
  let : IsElementaryAbelian 2 A := helem
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hnle : n ≤ 4 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (show 2 ^ n ≤ 2 ^ 4 from hn ▸ hbound)
  interval_cases n
  · exact (hne (card_eq_one.mp (by simpa using hn))).elim
  · exact Or.inl (by simpa using hn)
  · exact Or.inr (Or.inl (by simpa using hn))
  · exact Or.inr (Or.inr (by simpa using hn))
  · exact (h16 (by simpa using hn)).elim

end Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
