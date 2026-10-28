module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.LocalData
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.Reference
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.Marking

/-!
# Transport from the concrete fixed-free icosian reference cubic

The reference cubic has a checked irreducible quadratic on the whole binary
Leech module. Conjugation in the projective icosian model maps to conjugation
inside the literal tetrahedral centralizer. It therefore transports both
absence of fixed vectors and the cardinality of the full common centralizer.

The marked conjugacy is proved using the actual presentation comparison and
the checked generator orbits. Thus the marked root cubic is unconditionally
fixed-free for every supplied carrier equivalence. A faithful SL₃(4)
realization of the reference's full ambient common centralizer remains an
explicit input. The final conditional application connects that input to
`rootJ2_cubicGeometry_of_fixedFree_local_data`; relative cubic fusion
remains with its independent source owner.

Source: Aschbacher, *Sporadic Groups* (1994), 49.1–49.2, p.280,
and the proof of 49.5, p.283. Centralizers are in the Conway central quotient,
and all conjugators below lie in its actual subgroup C(I).
-/

@[expose] public noncomputable section

open Matrix Atlas.Conway Atlas.Codes Atlas.Lattices
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
open OctonionLocals RootModel

private theorem fixedFree_conjugate (a g : LeechCentralQuotient)
    (ha : CubicFixedFree a) : CubicFixedFree (MulAut.conj g a) := by
  intro v hv
  have he := congrArg (quotientModTwoRepresentation g⁻¹) hv
  have hf : quotientModTwoRepresentation a (quotientModTwoRepresentation g⁻¹ v) =
      quotientModTwoRepresentation g⁻¹ v := by
    simp only [MulAut.conj_apply, map_mul, map_inv, LinearEquiv.mul_apply] at he
    change (quotientModTwoRepresentation g).symm ((quotientModTwoRepresentation g)
      ((quotientModTwoRepresentation a) ((quotientModTwoRepresentation g).symm v))) =
      (quotientModTwoRepresentation g).symm v at he
    rw [map_inv]
    change (quotientModTwoRepresentation a) ((quotientModTwoRepresentation g).symm v) =
      (quotientModTwoRepresentation g).symm v
    simpa only [LinearEquiv.symm_apply_apply] using he
  apply (quotientModTwoRepresentation g⁻¹).injective
  rw [map_zero]
  exact ha _ hf

private theorem root_eq_conjugate
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (k : IcosianProjectiveModel)
    (hk : e Sporadic.LeechRelated.J2.RecognitionGeometry.x =
      MulAut.conj k referenceProjective) :
    rootJ2Cubic e = MulAut.conj (icosianProjectiveToCo1 k) referenceCubic := by
  unfold rootJ2Cubic
  rw [hk]
  simp only [MulAut.conj_apply, map_mul, map_inv, referenceCubic]

/-- A genuine marked-class comparison is enough for the fixed-vector assertion. -/
theorem rootJ2Cubic_fixedFree_of_referenceConjugacy
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (hmark : ∃ k : IcosianProjectiveModel,
      e Sporadic.LeechRelated.J2.RecognitionGeometry.x = MulAut.conj k referenceProjective) :
    CubicFixedFree (rootJ2Cubic e) := by
  obtain ⟨k, hk⟩ := hmark
  rw [root_eq_conjugate e k hk]
  exact fixedFree_conjugate _ _ referenceCubic_fixedFree

/-- The exact marked root cubic has no nonzero fixed vectors on the entire binary Leech module. -/
theorem rootJ2Cubic_fixedFree
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel) :
    CubicFixedFree (rootJ2Cubic e) :=
  rootJ2Cubic_fixedFree_of_referenceConjugacy e (rootCubic_referenceConjugacy e)

/-- Conjugacy in the actual icosian image preserves the full common centralizer order. -/
theorem rootJ2Cubic_centralizer_card_of_referenceConjugacy
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (hmark : ∃ k : IcosianProjectiveModel,
      e Sporadic.LeechRelated.J2.RecognitionGeometry.x = MulAut.conj k referenceProjective) :
    Nat.card ↥(centralizerI ⊓ Subgroup.centralizer
      (Subgroup.zpowers (rootJ2Cubic e) : Set LeechCentralQuotient)) =
      Nat.card referenceCentralizer := by
  obtain ⟨k, hk⟩ := hmark
  have he : Subgroup.zpowers (rootJ2Cubic e) = (Subgroup.zpowers referenceCubic).map
      (MulAut.conj (icosianProjectiveToCo1 k)).toMonoidHom := by
    rw [MonoidHom.map_zpowers, root_eq_conjugate e k hk]
    rfl
  rw [he, cubicCentralizer_card_conjugate _ (janko_mem_centralizerI k)]
  rfl

/-- The reference's faithful three-dimensional special-linear action gives the required bound. -/
theorem rootJ2Cubic_centralizer_card_le_of_referenceEmbedding
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (j : referenceCentralizer →* SL(3,F)) (hj : Function.Injective j) :
    Nat.card ↥(centralizerI ⊓ Subgroup.centralizer
      (Subgroup.zpowers (rootJ2Cubic e) : Set LeechCentralQuotient)) ≤ Nat.card SL(3,F) := by
  rw [rootJ2Cubic_centralizer_card_of_referenceConjugacy e (rootCubic_referenceConjugacy e)]
  exact Nat.card_le_card_of_injective j hj

/-- Actual application to the long-cubic geometry consumer, retaining the missing centralizer action. -/
theorem rootJ2_cubicGeometry_of_reference (L : LongFrame)
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (hfusion : FixedFreeCubicFusion)
    (j : referenceCentralizer →* SL(3,F)) (hj : Function.Injective j) :
    (∃ g ∈ centralizerI, (longCubic L).range ≤
      Sporadic.LeechRelated.J2.RecognitionGeometry.X.map (conjugatedRootJ2 e g)) ∧
    centralizerI ⊓ Subgroup.centralizer ((longCubic L).range : Set LeechCentralQuotient) ≤
      L.long.range :=
  rootJ2_cubicGeometry_of_fixedFree_local_data L e hfusion
    (rootJ2Cubic_fixedFree e)
    (rootJ2Cubic_centralizer_card_le_of_referenceEmbedding e j hj)

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
