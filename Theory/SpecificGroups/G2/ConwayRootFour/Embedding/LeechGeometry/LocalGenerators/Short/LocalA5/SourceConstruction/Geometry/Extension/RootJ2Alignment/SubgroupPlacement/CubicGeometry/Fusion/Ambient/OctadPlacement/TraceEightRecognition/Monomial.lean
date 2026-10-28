module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightRecognition.SignResolution

/-!
# Integral fusion after normalizing the coordinate permutation

Trace eight is the maximal trace of a signed permutation with eight fixed
coordinates. Equality forces all eight fixed signs to be positive. The
Golay coboundary calculation then conjugates any such involution to the
marked monomial element by a Golay sign. Its existing sextet conjugator
and octad transitivity finish fusion to the literal integral octad sign.

All conjugators preserve the full integral Leech lattice. Source:
Aschbacher, *Sporadic Groups* (1994), 25.1–25.5, pp.132–134, and
49.3–49.4, pp.280–282, retaining the trace-positive lift.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Codes Atlas.Lattices
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion

/-- Equality in the trace bound forces every fixed coordinate to have positive sign. -/
theorem traceEight_monomial_fixed_sign (m : GolayMonomialGroup)
    (hm : rationalLeechTrace (monomialEmbedding m) = 8)
    (hc : (Finset.univ.filter (fun i : Omega => m.right.val.symm i = i)).card = 8)
    (i : Omega) (hi : m.right.val.symm i = i) : m.left.toAdd.val i = 0 := by
  classical
  let f : Omega → ℚ := fun j => if m.right.val.symm j = j then 1 else 0
  let g : Omega → ℚ := fun j => if m.right.val.symm j = j then
    (if m.left.toAdd.val j = 0 then 1 else -1) else 0
  have hnonneg : ∀ j ∈ Finset.univ, 0 ≤ f j - g j := by
    intro j _
    dsimp [f, g]
    split_ifs <;> norm_num
  have he : ∑ j : Omega, (f j - g j) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hf : ∑ j, f j = 8 := by simp [f, hc]
    have hg : ∑ j, g j = 8 := (rationalLeechTrace_monomial m).symm.trans hm
    rw [hf, hg, sub_self]
  have he' := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp he i (Finset.mem_univ _)
  by_contra h
  norm_num [f, g, hi, h] at he'

/-- The marked nontrivial coordinate permutation has an octad of fixed points. -/
theorem normalGeneration_fixed_card :
    (Finset.univ.filter (fun i : Omega =>
      normalGenerationMonomial.right.val.symm i = i)).card = 8 := by decide +kernel

theorem normalGeneration_traceEight : TraceEightInvolution (monomialEmbedding normalGenerationMonomial) := by
  have he : normalGenerationCode = golayBasis 0 := by
    apply Subtype.ext
    rw [normalGenerationCode_val, golayBasis_coe]
    rfl
  have hc : monomialEmbedding normalGenerationMonomial = MulAut.conj zeta integralOctadSign := by
    rw [normalGenerationMonomial_image]
    change zeta * signEmbedding (Multiplicative.ofAdd normalGenerationCode) * zeta⁻¹ = _
    rw [he]
    rfl
  constructor
  · rw [hc, ← map_pow, integralOctadSign_sq, map_one]
  · rw [hc, rationalLeechTrace_conj, integralOctadSign_trace]

/-- All trace-eight lifts of the marked coordinate permutation are conjugate
by an actual Golay sign, so the sextet isometry supplies their integral fusion. -/
theorem traceEight_monomial_isConj_of_right_eq (m : GolayMonomialGroup)
    (hm : TraceEightInvolution (monomialEmbedding m))
    (hp : m.right = normalGenerationMonomial.right) :
    IsConj (monomialEmbedding m) integralOctadSign := by
  let c := m.left.toAdd + normalGenerationMonomial.left.toAdd
  have hinv : ∀ i, c.val (normalGenerationMonomial.right.val.symm i) = c.val i := by
    intro i
    have h := traceEight_monomial_sign_invariant m hm.1 i
    rw [hp] at h
    change m.left.toAdd.val _ + normalGenerationMonomial.left.toAdd.val _ = _
    rw [h, traceEight_monomial_sign_invariant normalGenerationMonomial normalGeneration_traceEight.1]
    rfl
  have hfix : ∀ i, normalGenerationMonomial.right.val.symm i = i → c.val i = 0 := by
    intro i hi
    change m.left.toAdd.val i + normalGenerationMonomial.left.toAdd.val i = 0
    rw [traceEight_monomial_fixed_sign m hm.2 (by rw [hp]; exact normalGeneration_fixed_card)
      i (by rw [hp]; exact hi),
      traceEight_monomial_fixed_sign normalGenerationMonomial normalGeneration_traceEight.2
        normalGeneration_fixed_card i hi, add_zero]
  obtain ⟨b, hb⟩ := TraceEightSigns.fixed_zero_sign_eq_coboundary c hinv hfix
  have he : signIsometry b * monomialEmbedding m =
      monomialEmbedding normalGenerationMonomial * signIsometry b := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    funext i
    change (if b.val i = 0 then ((monomialEmbedding m).val x).val i
      else -((monomialEmbedding m).val x).val i) =
      ((monomialEmbedding normalGenerationMonomial).val ((signIsometry b).val x)).val i
    rw [monomialEmbedding_apply, hp, monomialEmbedding_apply]
    change (if b.val i = 0 then
        (if m.left.toAdd.val i = 0 then x.val (normalGenerationMonomial.right.val.symm i)
          else -x.val (normalGenerationMonomial.right.val.symm i))
      else -(if m.left.toAdd.val i = 0 then x.val (normalGenerationMonomial.right.val.symm i)
          else -x.val (normalGenerationMonomial.right.val.symm i))) =
      (if normalGenerationMonomial.left.toAdd.val i = 0 then
        (if b.val (normalGenerationMonomial.right.val.symm i) = 0 then
          x.val (normalGenerationMonomial.right.val.symm i)
          else -x.val (normalGenerationMonomial.right.val.symm i))
      else -(if b.val (normalGenerationMonomial.right.val.symm i) = 0 then
          x.val (normalGenerationMonomial.right.val.symm i)
          else -x.val (normalGenerationMonomial.right.val.symm i)))
    have h := hb i
    change b.val i + b.val (normalGenerationMonomial.right.val.symm i) =
      m.left.toAdd.val i + normalGenerationMonomial.left.toAdd.val i at h
    rcases bit_cases (b.val i) with h₁ | h₁ <;>
      rcases bit_cases (b.val (normalGenerationMonomial.right.val.symm i)) with h₂ | h₂ <;>
      rcases bit_cases (m.left.toAdd.val i) with h₃ | h₃ <;>
      rcases bit_cases (normalGenerationMonomial.left.toAdd.val i) with h₄ | h₄ <;> simp_all
  have hc : IsConj (monomialEmbedding m) (monomialEmbedding normalGenerationMonomial) :=
    isConj_iff.mpr ⟨signIsometry b, by rw [he]; simp [mul_assoc]⟩
  exact hc.trans normalGenerationMonomial_isConj_integralOctadSign

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
