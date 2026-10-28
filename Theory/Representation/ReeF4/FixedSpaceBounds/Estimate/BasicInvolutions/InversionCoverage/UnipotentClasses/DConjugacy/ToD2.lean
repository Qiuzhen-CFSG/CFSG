module
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.Reduction
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.ToD2.Coordinates
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.ToD2.Weyl

/-!
# Transport square-one Ree D words into D₂

If the Y₁ coordinate is nonzero, conjugation by x₈ clears the X₃ main
coordinate. The square equations then force the X₆ and Y₇ coordinates to
vanish, and the fixed linear Weyl representative carries D₁ into D₂.
The same reflection handles a nonzero Y₇ coordinate. If both Y endpoints
vanish, squaring kills both middle main coordinates; x₈ conjugation clears
X₆ whenever X₂ is nonzero. The case X₂ = 0 is already in D₂.

Every conjugator lies in the actual exceptional-twist fixed model. No
involution classification, root-class count, or tail compression is used.
Source: GLS3 Table 2.4 and 2.4.5(d), with the literal D, D₁ and D₂ sections
of Lemma 3.3.9. This supplies the first transport in `DConjugacy.Reduction`.
-/
public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy
open Parabolics ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
open Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics.Binary.FixedGeometry
open ToD2

private def Reaches (m : ℕ) (x : Model m) : Prop :=
  ∃ (g : Model m) (q : PositiveParameters m), D₂Support q ∧
    g * x * g⁻¹ = wordElement m q

private theorem reaches_of_conj (m : ℕ) (x y g : Model m)
    (hxy : g * x * g⁻¹ = y) (hy : Reaches m y) : Reaches m x := by
  obtain ⟨h, q, hq, he⟩ := hy
  refine ⟨h * g, q, hq, ?_⟩
  calc
    _ = h * (g * x * g⁻¹) * h⁻¹ := by group
    _ = _ := by rw [hxy, he]

private theorem conjugate_sq (m : ℕ) (g x : Model m) (hx : x ^ 2 = 1) :
    (g * x * g⁻¹) ^ 2 = 1 := by
  simpa only [map_pow, map_one, MulAut.conj_apply] using congrArg (MulAut.conj g) hx

private theorem reaches_of_D₁ (m : ℕ) (p : PositiveParameters m) (hp : D₁Support p) :
    Reaches m (wordElement m p) := by
  obtain ⟨q, hq, he, hc, ha⟩ := linear_transport m p hp.1
  exact ⟨weylLift m .linear, q, ⟨hq, ha.trans hp.2.1, hc.trans hp.2.2⟩, he⟩

private theorem half_ne_zero (m : ℕ) {a : CoefficientField m} (ha : a ≠ 0) :
    halfFrobenius m a ≠ 0 := by
  intro h
  exact ha ((halfFrobenius m).injective (by simpa only [map_zero] using h))

private theorem zero_of_mul_half (m : ℕ) {a : CoefficientField m}
    (h : a * halfFrobenius m a = 0) : a = 0 := by
  rcases mul_eq_zero.mp h with ha | ha
  · exact ha
  · exact (halfFrobenius m).injective (by simpa only [map_zero] using ha)

private theorem reaches_of_first_nonzero (m : ℕ) (p : PositiveParameters m)
    (hp : DSupport p) (hsq : wordElement m p ^ 2 = 1) (hd : p.central 0 ≠ 0) :
    Reaches m (wordElement m p) := by
  let t := p.main 3 / p.central 0
  obtain ⟨q, hq, he, hdq, hhq, -, -⟩ := eighth_transport m p hp t
  have hsq' : wordElement m q ^ 2 = 1 := by
    rw [← he]
    exact conjugate_sq m _ _ hsq
  have hh : q.main 3 = 0 := by
    rw [hhq, div_mul_cancel₀ _ hd, CharTwo.add_self_eq_zero]
  have hd' : q.central 0 ≠ 0 := by rwa [hdq]
  obtain ⟨h₁, h₂, h₃⟩ := square_equations m q hq hsq'
  have hg : q.central 2 = 0 := by
    have hz : q.central 2 * q.central 0 = 0 := by simpa only [hh, mul_zero, zero_add] using h₁
    exact (mul_eq_zero.mp hz).resolve_right hd'
  have he0 : q.main 1 = 0 := by
    apply zero_of_mul_half m
    simpa only [hh, hg, map_zero, zero_mul, mul_zero, add_zero, zero_add] using h₂
  have hb : q.pair 2 = 0 := by
    have hz : halfFrobenius m (q.pair 2) * halfFrobenius m (q.central 0) = 0 := by
      simpa only [he0, hh, hg, map_zero, zero_mul, mul_zero, add_zero, zero_add] using h₃
    have hz' := (mul_eq_zero.mp hz).resolve_right (half_ne_zero m hd')
    exact (halfFrobenius m).injective (by simpa only [map_zero] using hz')
  exact reaches_of_conj m _ _ _ he (reaches_of_D₁ m q ⟨hq, hb, hg⟩)

private theorem reaches_of_zero_endpoints (m : ℕ) (p : PositiveParameters m)
    (hp : DSupport p) (hsq : wordElement m p ^ 2 = 1)
    (hd : p.central 0 = 0) (hg : p.central 2 = 0) : Reaches m (wordElement m p) := by
  obtain ⟨h₁, h₂, h₃⟩ := square_equations m p hp hsq
  have hprod : p.main 1 * p.main 3 = 0 := by simpa only [hd, mul_zero, add_zero] using h₁
  have hh : p.main 3 = 0 := by
    rcases mul_eq_zero.mp hprod with he | hh
    · apply zero_of_mul_half m
      simpa only [he, hd, hg, map_zero, zero_mul, mul_zero, zero_add, add_zero] using h₃
    · exact hh
  have he : p.main 1 = 0 := by
    apply zero_of_mul_half m
    simpa only [hh, hd, hg, map_zero, zero_mul, mul_zero, zero_add, add_zero] using h₂
  by_cases ha : p.pair 1 = 0
  · exact ⟨1, p, ⟨hp, ha, hd⟩, by simp⟩
  · let t := halfFrobenius m (p.pair 2) / halfFrobenius m (p.pair 1)
    obtain ⟨q, hq, hconj, -, -, hbq, hgq⟩ := eighth_transport m p hp t
    have hb : q.pair 2 = 0 := by
      apply (halfFrobenius m).injective
      rw [map_zero, hbq]
      simp only [hd, hh, mul_zero, add_zero]
      rw [div_mul_cancel₀ _ (half_ne_zero m ha), CharTwo.add_self_eq_zero]
    have hg' : q.central 2 = 0 := by simp only [hgq, hg, he, hh, hd, zero_mul, mul_zero, add_zero]
    exact reaches_of_conj m _ _ _ hconj (reaches_of_D₁ m q ⟨hq, hb, hg'⟩)

/-- Every square-one D word is conjugate into D₂ inside the actual fixed Ree group. -/
theorem transportToD₂ (m : ℕ) (_hm : 1 ≤ m) : TransportToD₂ m := by
  intro p hp hsq
  change Reaches m (wordElement m p)
  by_cases hd : p.central 0 = 0
  · by_cases hg : p.central 2 = 0
    · exact reaches_of_zero_endpoints m p hp hsq hd hg
    · obtain ⟨q, hq, he, hdq, -⟩ := linear_transport m p hp
      apply reaches_of_conj m _ _ _ he
      apply reaches_of_first_nonzero m q hq
      · rw [← he]
        exact conjugate_sq m _ _ hsq
      · rwa [hdq]
  · exact reaches_of_first_nonzero m p hp hsq hd

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy
