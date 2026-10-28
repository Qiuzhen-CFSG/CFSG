module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.Bounds

/-!
# Transport of literal fixed-space bounds between native octads

Native M₂₄ transitivity and surjectivity of the certified quotient map lift
octad conjugacy into the literal max1 subgroup. Conjugation preserves the
intrinsic two-core and identifies the respective centralizers. Hence the two
bounds for the seed octad imply the bounds for every native octad.

Source: the E₂¹¹.M₂₄ local subgroup in GLS3 Table 5.3i and the local
configuration in Aschbacher–Smith A.3.12(17), used in 1.3.9.
-/

public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement

private theorem fixedCard_equiv {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (s : Set G) :
    Nat.card ((centralizer s).subgroupOf (pCore 2 G)) =
      Nat.card ((centralizer (e '' s)).subgroupOf (pCore 2 G')) := by
  apply Nat.card_congr
  refine {
    toFun := fun x => ⟨⟨e x.val.val, ?_⟩, ?_⟩
    invFun := fun y => ⟨⟨e.symm y.val.val, ?_⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [← pCore_map_iso 2 e]
    exact mem_map_of_mem e.toMonoidHom x.val.property
  · rintro _ ⟨z, hz, rfl⟩
    exact (map_mul e z x.val.val).symm.trans
      ((congrArg e (x.property z hz)).trans (map_mul e x.val.val z))
  · rw [← pCore_map_iso 2 e.symm]
    exact mem_map_of_mem e.symm.toMonoidHom y.val.property
  · intro z hz
    change z * e.symm y.val.val = e.symm y.val.val * z
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply, Subgroup.subtype_apply] using
      y.property (e z) (Set.mem_image_of_mem e hz)
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    exact e.symm_apply_apply _
  · intro y
    apply Subtype.ext
    apply Subtype.ext
    exact e.apply_symm_apply _

attribute [local irreducible] Janko4.modelGroup certifiedMathieuSubgroup

theorem literalOctadTwoPreimage_map_conj (g : certifiedMathieuSubgroup) (O O' : Octad)
    (hO : literalMathieuMap g • O.val = O'.val) :
    (literalOctadTwoPreimage O).map (MulAut.conj g).toMonoidHom =
      literalOctadTwoPreimage O' := by
  have hs : octadStabilizer O' =
      (octadStabilizer O).map (MulAut.conj (literalMathieuMap g)).toMonoidHom := by
    change MulAction.stabilizer M24 O'.val =
      (MulAction.stabilizer M24 O.val).map _
    rw [← hO, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  have hc : (octadStabilizer O').pCoreIn 2 =
      ((octadStabilizer O).pCoreIn 2).map
        (MulAut.conj (literalMathieuMap g)).toMonoidHom := by
    rw [hs, map_pCoreIn_of_injective 2 _ _ (MulAut.conj _).injective]
  ext x
  rw [mem_map_equiv]
  change literalMathieuMap ((MulAut.conj g).symm x) ∈ (octadStabilizer O).pCoreIn 2 ↔
    literalMathieuMap x ∈ (octadStabilizer O').pCoreIn 2
  rw [hc, mem_map_equiv]
  simp only [MulAut.conj_symm_apply, map_mul, map_inv]

/-- All native octads follow from the element bound on the chosen native octad. -/
theorem literalOctad_elementFixedBound_of_seed
    (h : ∀ x : certifiedMathieuSubgroup,
      x ∈ literalOctadTwoPreimage LinearFourCore.seedOctad →
      x ∉ pCore 2 certifiedMathieuSubgroup →
      Nat.card ((centralizer ({x} : Set certifiedMathieuSubgroup)).subgroupOf
        (pCore 2 certifiedMathieuSubgroup)) ≤ 128) : LiteralOctadElementFixedBound := by
  intro O x hx hnx
  obtain ⟨q, hq⟩ := exists_smul_octad_eq LinearFourCore.seedOctad O
  obtain ⟨g, rfl⟩ := literalMathieuMap_surjective q
  let e := MulAut.conj g
  have hm : (literalOctadTwoPreimage LinearFourCore.seedOctad).map e.toMonoidHom =
      literalOctadTwoPreimage O := by
    exact literalOctadTwoPreimage_map_conj g LinearFourCore.seedOctad O hq
  have hx' : e.symm x ∈ literalOctadTwoPreimage LinearFourCore.seedOctad := by
    exact mem_map_equiv.mp (hm.symm ▸ hx)
  have hnx' : e.symm x ∉ pCore 2 certifiedMathieuSubgroup := by
    intro hn
    apply hnx
    rw [← pCore_map_iso 2 e]
    exact ⟨e.symm x, hn, e.apply_symm_apply x⟩
  have he := fixedCard_equiv e ({e.symm x} : Set certifiedMathieuSubgroup)
  rw [Set.image_singleton, e.apply_symm_apply] at he
  exact he ▸ h (e.symm x) hx' hnx'

/-- Surjectivity of the actual quotient map lifts native octad conjugacy. -/
theorem literalOctad_commonFixedBound_of_seed
    (h : Nat.card ((centralizer
      (literalOctadTwoPreimage LinearFourCore.seedOctad : Set certifiedMathieuSubgroup)).subgroupOf
      (pCore 2 certifiedMathieuSubgroup)) < 128) : LiteralOctadCommonFixedBound := by
  intro O
  obtain ⟨q, hq⟩ := exists_smul_octad_eq LinearFourCore.seedOctad O
  obtain ⟨g, rfl⟩ := literalMathieuMap_surjective q
  have hm : (literalOctadTwoPreimage LinearFourCore.seedOctad).map
      (MulAut.conj g).toMonoidHom = literalOctadTwoPreimage O := by
    exact literalOctadTwoPreimage_map_conj g LinearFourCore.seedOctad O hq
  have he := fixedCard_equiv (MulAut.conj g)
    (literalOctadTwoPreimage LinearFourCore.seedOctad : Set certifiedMathieuSubgroup)
  change Nat.card _ = Nat.card ((centralizer
    (((literalOctadTwoPreimage LinearFourCore.seedOctad).map
      (MulAut.conj g).toMonoidHom) : Set certifiedMathieuSubgroup)).subgroupOf _) at he
  rw [hm] at he
  exact he ▸ h

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
