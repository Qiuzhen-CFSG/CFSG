/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/QuotientGolaySigns.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.GolaySignNormalClosure
public import Theory.AtlasPort.OtherSporadic.Conway.MonomialQuotientSplitting

/-!
The abelian Golay sign subgroup of the central quotient.
The proof transports the concrete sign embedding, relative normality, and normal generation through the quotient.

Source: Gerald Höhn, `Atlas/Conway/QuotientGolaySigns.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

def quotientGolaySignEmbedding : GolaySignQuotient →* LeechCentralQuotient :=
  quotientMonomialSubgroup.subtype.comp quotientMonomialSigns

theorem quotientGolaySignEmbedding_injective : Function.Injective quotientGolaySignEmbedding :=
  Subtype.val_injective.comp quotientMonomialSigns_injective

def quotientGolaySignSubgroup : Subgroup LeechCentralQuotient := quotientGolaySignEmbedding.range

def quotientGolaySignEquiv : GolaySignQuotient ≃* quotientGolaySignSubgroup :=
  MonoidHom.ofInjective quotientGolaySignEmbedding_injective

theorem quotientGolaySignEmbedding_compatible (c : Multiplicative golay) :
    quotientGolaySignEmbedding (golaySignProjection c) = leechCentralProjection (signEmbedding c) :=
  quotientMonomialSigns_compatible c

theorem quotientGolaySignSubgroup_eq_map :
    quotientGolaySignSubgroup = golaySignSubgroup.map leechCentralProjection := by
  ext g
  constructor
  · rintro ⟨c,rfl⟩
    obtain ⟨d,rfl⟩ := QuotientGroup.mk'_surjective golayOneSubgroup c
    exact ⟨signEmbedding d,⟨d,rfl⟩,(quotientGolaySignEmbedding_compatible d).symm⟩
  · rintro ⟨g,⟨c,rfl⟩,rfl⟩
    exact ⟨golaySignProjection c,quotientGolaySignEmbedding_compatible c⟩

theorem quotientGolaySignSubgroup_eq_map_range :
    quotientGolaySignSubgroup = quotientMonomialSigns.range.map quotientMonomialSubgroup.subtype := by
  exact MonoidHom.range_comp _ _

theorem quotientGolaySignSubgroup_le_monomial : quotientGolaySignSubgroup ≤ quotientMonomialSubgroup := by
  rintro x ⟨c,rfl⟩
  exact (quotientMonomialSigns c).prop

theorem quotientGolaySignSubgroup_normal :
    (quotientGolaySignSubgroup.subgroupOf quotientMonomialSubgroup).Normal := by
  have he : quotientGolaySignSubgroup.subgroupOf quotientMonomialSubgroup =
      quotientMonomialSigns.range := by
    change quotientGolaySignSubgroup.comap quotientMonomialSubgroup.subtype = _
    rw [quotientGolaySignSubgroup_eq_map_range]
    exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
  rw [he,← quotientMonomialRetraction_kernel]
  infer_instance

theorem quotientGolaySignSubgroup_abelian : IsMulCommutative quotientGolaySignSubgroup := by
  apply IsMulCommutative.of_comm
  intro x y
  obtain ⟨c,hc⟩ := quotientGolaySignEquiv.surjective x
  obtain ⟨d,hd⟩ := quotientGolaySignEquiv.surjective y
  rw [← hc,← hd]
  simpa only [map_mul] using congrArg quotientGolaySignEquiv (mul_comm c d)

theorem quotientGolaySigns_normalClosure_eq_full :
    Subgroup.normalClosure (quotientGolaySignSubgroup : Set LeechCentralQuotient) = ⊤ := by
  rw [quotientGolaySignSubgroup_eq_map,Subgroup.coe_map,
    ← Subgroup.map_normalClosure _ _ leechCentralProjection_surjective]
  change golaySignNormalClosure.map leechCentralProjection = ⊤
  rw [golaySign_normalClosure_eq_full,← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top_of_surjective _ leechCentralProjection_surjective

end Atlas.Conway
