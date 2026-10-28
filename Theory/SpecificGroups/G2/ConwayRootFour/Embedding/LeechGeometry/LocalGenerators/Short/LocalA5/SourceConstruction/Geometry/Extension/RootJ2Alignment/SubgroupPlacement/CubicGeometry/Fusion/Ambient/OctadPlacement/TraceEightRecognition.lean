module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.Spectral
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightRecognition.Monomial
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightRecognition.Mathieu

/-!
# Recognition of integral Leech involutions of trace eight

An involution fixes a Leech cross because the number of crosses is odd.
An integral isometry moves this cross to the coordinate cross, making the
involution a signed Golay permutation. Trace eight gives fixed coordinates.
If its permutation is trivial, octad transitivity finishes the argument.
Otherwise the actual Mathieu involution classification normalizes the
permutation. A checked Golay coboundary identity resolves the signs, and
the existing sextet isometry conjugates the resulting representative to a
weight-eight Golay sign. All these operations preserve the full Leech lattice.

This proves the recognition input consumed by
`integralOctadPlacement_of_traceEight`; it uses no cubic placement or fusion
premise. Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5,
pp.132–134, and 49.3–49.4, pp.280–282. Section 25 uses the complementary
sign lift; the conclusion here is the literal trace-positive weight-eight
lift `signEmbedding (Multiplicative.ofAdd (golayBasis 0))`.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Codes Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion

/-- Permutation normalization lifts to the actual semidirect product, after
which the proved Golay sign calculation gives integral conjugacy. -/
theorem traceEight_monomial_isConj_of_coordinate_conjugacy (m : GolayMonomialGroup)
    (hm : TraceEightInvolution (monomialEmbedding m))
    (hp : IsConj m.right normalGenerationMonomial.right) :
    IsConj (monomialEmbedding m) integralOctadSign := by
  obtain ⟨p, hp⟩ := isConj_iff.mp hp
  let u : GolayMonomialGroup := SemidirectProduct.inr p
  let n : GolayMonomialGroup := u * m * u⁻¹
  have hn : n.right = normalGenerationMonomial.right := by
    simpa [n, u] using hp
  have hc : MulAut.conj (monomialEmbedding u) (monomialEmbedding m) = monomialEmbedding n := by
    simp [n, MulAut.conj_apply]
  have ht : TraceEightInvolution (monomialEmbedding n) := by
    constructor
    · rw [← hc, ← map_pow, hm.1, map_one]
    · rw [← hc, rationalLeechTrace_conj, hm.2]
  exact (isConj_iff.mpr ⟨monomialEmbedding u, hc⟩).trans
    (traceEight_monomial_isConj_of_right_eq n ht hn)

/-- Recognize every trace-eight signed Golay involution inside the integral
Leech isometry group. Both permutation and sign conjugators are constructed. -/
theorem traceEight_monomial_isConj (m : GolayMonomialGroup)
    (hm : TraceEightInvolution (monomialEmbedding m)) :
    IsConj (monomialEmbedding m) integralOctadSign := by
  classical
  by_cases hp : m.right = 1
  · have he : monomialEmbedding m = signIsometry m.left.toAdd := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      apply Subtype.ext
      funext i
      rw [monomialEmbedding_apply, hp]
      rfl
    rw [he]
    exact traceEight_sign_isConj m.left.toAdd (he ▸ hm.2)
  · have hf : ∃ i : Omega, m.right.val.symm i = i := by
      obtain ⟨i, hi⟩ := Finset.card_pos.mp
        (lt_of_lt_of_le (by decide : 0 < 8) (traceEight_monomial_fixed_card m hm.2))
      exact ⟨i, (Finset.mem_filter.mp hi).2⟩
    exact traceEight_monomial_isConj_of_coordinate_conjugacy m hm
      (mathieu_fixed_involution_isConj_normalGeneration m.right
        (traceEight_monomial_involutive m hm.1) hp hf)

/-- An involution of rational trace eight is conjugate to the literal
weight-eight Golay sign by an isometry of the full integral Leech lattice. -/
theorem traceEightInvolutionRecognition : TraceEightInvolutionRecognition := by
  intro t ht
  obtain ⟨m, hm, h, hh⟩ := traceEight_exists_monomial t ht
  have hc : IsConj t integralOctadSign :=
    (isConj_iff.mpr ⟨h, hh⟩).trans (traceEight_monomial_isConj m hm)
  exact isConj_iff.mp hc

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
