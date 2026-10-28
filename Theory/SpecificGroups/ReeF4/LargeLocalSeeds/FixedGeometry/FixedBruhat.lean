module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.QuotientGeometry.Factorization
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.Overlap
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.Overlap.NormalizerWords
public import Mathlib.GroupTheory.Sylow

/-!
# Odd index and generation for the fixed Ree root subgroups

The proved fixed Bruhat factorization and torus calculations reduce both
remaining conclusions to two split matrix facts: normalizer words have genuine
Weyl monomial actions, and their height-triangular elements belong to the diagonal
torus. The checked normalizer-word theorems establish both facts, using the proved
equality of the coroot-word torus and the diagonal torus.

For the index calculation, the Borel is the normalizer of the fixed positive
subgroup. Its relative index is odd because its torus has odd order. The
two-group action on cosets identifies the parity of this relative index with
that of the ambient index. No order formula for the Ree group is required.

For generation, both relative Weyl representatives belong to their marked
seeds. The fixed torus normalizes each seed, so Bruhat factorization makes
their join normal in the fixed group. An actual nonzero simple-root matrix
entry proves that this join is nontrivial; the permitted simplicity hypothesis
then makes it the whole group. The matrix-preserving comparison transports
both results to the supplied `LocalBlockInput` and its actual fixed intersections.

The conditional reductions are retained, and the final two theorems discharge
their matrix hypotheses. Odd index holds for every parameter, including the full
binary fixed group. Generation assumes simplicity of the supplied fixed group,
as permitted for the large Ree family. These are the Sylow-index and generation
ingredients of the source amalgam; no quotient or radical identification is
asserted here.
Source: GLS3, 1.11.5 and 2.3.2–5, `refs/KGroup/GLS3/Chapter1.tex` and
`refs/KGroup/GLS3/chapter2.tex`; the Ree amalgam in Aschbacher–Smith,
F.1.12(I)(5) and (II), printed pp.263–264, and its generation use in 2.3.9(7),
printed p.526 of `refs/quasithin.pdf`.
-/

public section

open Subgroup
open scoped Pointwise

namespace ReeF4.LargeLocalSeeds.FixedBruhat
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics SectionGeometry.BNPair Parabolics.Binary.FixedGeometry
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open NormalizerGeometry

variable {m : ℕ}
variable (hweyl : ∀ n ∈ splitNormalizerWords m,
    ∃ (w : typeF4RootPairing.weylGroup) (c : F4Chevalley.Root → (CoefficientField m)ˣ),
      RootMonomial n.val.val (typeF4RootPairing.weylGroupToPerm w) c)
variable (hkernel : ∀ n ∈ splitNormalizerWords m,
    Overlap.IsHeightTriangular n → n ∈ diagonalTorus m)

private theorem fixedTorus_le_unipotent_normalizer (m : ℕ) :
    fixedTorus m ≤ normalizer (unipotent m) :=
  (comap_mono (splitTorus_normalizes_unipotent m)).trans
    ((splitUnipotent m).le_normalizer_comap (toSplitGroup m))

private theorem fixedTorus_le_seed_normalizer (m : ℕ) (s : Side) :
    fixedTorus m ≤ normalizer (seed m s) := by
  have h : splitTorus m ≤ normalizer (splitSeed m s) := by
    rw [splitTorus_eq_diagonalTorus]
    exact diagonalTorus_le_seed_normalizer m s
  exact (comap_mono h).trans ((splitSeed m s).le_normalizer_comap (toSplitGroup m))

include hweyl hkernel in
private theorem model_normalizer_eq_borel : normalizer (unipotent m) = borel m := by
  apply le_antisymm
  · exact Overlap.unipotent_normalizer_le_borel_of_normalizerWords m
      (splitTorus_eq_diagonalTorus m) hkernel hweyl
  · rw [borel_eq_unipotent_sup_fixedTorus]
    exact sup_le (unipotent m).le_normalizer (fixedTorus_le_unipotent_normalizer m)

private theorem relIndex_sup_of_normalizes {G : Type*} [Group G]
    (U T : Subgroup G) (h : T ≤ normalizer U) : U.relIndex (U ⊔ T) = U.relIndex T := by
  let B := U ⊔ T
  have : (U.subgroupOf B).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le U.le_normalizer h)
  have he := relIndex_sup_left (T.subgroupOf B) (U.subgroupOf B)
  rw [← subgroupOf_sup le_sup_left le_sup_right,
    relIndex_subgroupOf (show U ⊔ T ≤ B from le_rfl),
    relIndex_subgroupOf (show T ≤ B from le_sup_right)] at he
  exact he

private theorem odd_index_of_odd_normalizer {G : Type*} [Group G] [Finite G]
    (U : Subgroup G) (hU : IsPGroup 2 U)
    (ho : Odd (U.relIndex (normalizer U))) : Odd U.index := by
  have hc := hU.card_modEq_card_fixedPoints (G ⧸ U)
  rw [Nat.card_congr (Sylow.fixedPointsMulLeftCosetsEquivQuotient U)] at hc
  change U.index % 2 = U.relIndex (normalizer U) % 2 at hc
  rw [Nat.odd_iff] at ho ⊢
  exact hc.trans ho

include hweyl hkernel in
/-- The two normalizer-word matrix facts imply odd index for the positive subgroup. -/
private theorem model_unipotent_index_odd : Odd (unipotent m).index := by
  have hu : IsPGroup 2 (unipotent m) :=
    (splitUnipotent_isPGroup m).comap_of_injective (toSplitGroup m) (toSplitGroup_injective m)
  apply odd_index_of_odd_normalizer _ hu
  rw [model_normalizer_eq_borel hweyl hkernel, borel_eq_unipotent_sup_fixedTorus,
    relIndex_sup_of_normalizes _ _ (fixedTorus_le_unipotent_normalizer m)]
  exact (fixedTorus_odd_card m (splitTorus_card_odd m)).of_dvd_nat (relIndex_dvd_card _ _)

private theorem model_unipotent_ne_bot (m : ℕ) : unipotent m ≠ ⊥ := by
  obtain ⟨x, hx, j, hj⟩ := Overlap.FixedWitnesses.exists_simple_coordinate m 0
  intro he
  have hx1 : x = 1 := mem_bot.mp (he ▸ hx)
  subst x
  apply hj
  simp

include hweyl hkernel in
/-- The join of both seeds is normal once the normalizer words have their
factorization into a fixed torus element and fixed Weyl words. -/
private theorem model_seed_sup_normal : (seed m .suzuki ⊔ seed m .linear).Normal := by
  let H := seed m .suzuki ⊔ seed m .linear
  have hU : unipotent m ≤ H := (unipotent_le_seed m .suzuki).trans le_sup_left
  have hW : weylSubgroup m ≤ H := weylSubgroup_le_seeds m
  have hT : fixedTorus m ≤ normalizer H :=
    (le_inf (fixedTorus_le_seed_normalizer m .suzuki)
      (fixedTorus_le_seed_normalizer m .linear)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hB : borel m ≤ normalizer H := by
    rw [borel_eq_unipotent_sup_fixedTorus]
    exact sup_le (hU.trans H.le_normalizer) hT
  have hN : normalizerWords m ≤ normalizer H :=
    (normalizerWords_le_fixedTorus_sup_weylSubgroup_of_monomial m hweyl hkernel).trans
      (sup_le hT (hW.trans H.le_normalizer))
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← borel_sup_normalizerWords m]
  exact sup_le hB hN

include hweyl hkernel in
/-- Simplicity removes the possible proper normal join of the two fixed seeds. -/
private theorem model_seed_sup_eq_top [IsSimpleGroup (Model m)] :
    seed m .suzuki ⊔ seed m .linear = ⊤ := by
  rcases (model_seed_sup_normal hweyl hkernel).eq_bot_or_eq_top with h | h
  · exfalso
    apply model_unipotent_ne_bot m
    exact bot_unique (h ▸ ((unipotent_le_seed m .suzuki).trans
      (le_sup_left : seed m .suzuki ≤ seed m .suzuki ⊔ seed m .linear)))
  · exact h

private theorem fixedIntersection_map (d : LocalBlockInput m) (H : Subgroup (SplitGroup m)) :
    (H.subgroupOf d.fixedGroup).map d.modelEquiv.toMonoidHom = H.comap (toSplitGroup m) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change toSplitGroup m (d.modelEquiv y) ∈ H
    simpa only [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe] using (show y.val ∈ H from hy)
  · intro hx
    refine ⟨d.modelEquiv.symm x, ?_, d.modelEquiv.apply_symm_apply x⟩
    change (d.modelEquiv.symm x).val ∈ H
    rw [← LocalBlockInput.modelEquiv_coe, d.modelEquiv.apply_symm_apply]
    simpa only [mem_comap, toSplitGroup_apply] using hx

include hweyl hkernel in
/-- Odd index transfers along the comparison preserving the actual matrices. -/
theorem standardUnipotent_index_odd_of_normalizer_geometry (d : LocalBlockInput m) :
    Odd (standardUnipotent d).index := by
  rw [← (standardUnipotent d).index_map_equiv d.modelEquiv]
  change Odd ((splitUnipotent m).subgroupOf d.fixedGroup |>.map d.modelEquiv.toMonoidHom).index
  rw [fixedIntersection_map]
  exact model_unipotent_index_odd hweyl hkernel

include hweyl hkernel in
/-- Generation transfers to the two actual fixed intersections in the supplied group. -/
theorem standardSeed_sup_eq_top_of_normalizer_geometry (d : LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] : standardSeed d .suzuki ⊔ standardSeed d .linear = ⊤ := by
  let : IsSimpleGroup (Model m) := d.modelEquiv.symm.isSimpleGroup
  apply (map_injective (f := d.modelEquiv.toMonoidHom) d.modelEquiv.injective)
  rw [Subgroup.map_sup]
  change ((splitSeed m .suzuki).subgroupOf d.fixedGroup).map d.modelEquiv.toMonoidHom ⊔
    ((splitSeed m .linear).subgroupOf d.fixedGroup).map d.modelEquiv.toMonoidHom = _
  rw [fixedIntersection_map, fixedIntersection_map, map_top_of_surjective _ d.modelEquiv.surjective]
  exact model_seed_sup_eq_top hweyl hkernel

/-- The actual positive fixed subgroup has odd index, for every Ree parameter. -/
theorem standardUnipotent_index_odd (d : LocalBlockInput m) :
    Odd (standardUnipotent d).index :=
  standardUnipotent_index_odd_of_normalizer_geometry
    (fun _ hn => Overlap.normalizerWords_weylMonomial (splitTorus_eq_diagonalTorus m) hn)
    (fun _ hn htri => Overlap.normalizerWord_mem_diagonalTorus_of_heightTriangular
      (splitTorus_eq_diagonalTorus m) hn htri) d

/-- In the simple fixed group, the actual Suzuki and linear root seeds generate.
The Suzuki seed uses nodes `{1, 2}` and the linear seed uses nodes `{0, 3}`. -/
theorem standardSeed_sup_eq_top (d : LocalBlockInput m) [IsSimpleGroup d.fixedGroup] :
    standardSeed d .suzuki ⊔ standardSeed d .linear = ⊤ :=
  standardSeed_sup_eq_top_of_normalizer_geometry
    (fun _ hn => Overlap.normalizerWords_weylMonomial (splitTorus_eq_diagonalTorus m) hn)
    (fun _ hn htri => Overlap.normalizerWord_mem_diagonalTorus_of_heightTriangular
      (splitTorus_eq_diagonalTorus m) hn htri) d

end ReeF4.LargeLocalSeeds.FixedBruhat

end
