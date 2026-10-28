module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.BruhatCoverage.Basic
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.SplitGeneration

/-!
# Binary split generation by the positive subgroup and Weyl words

Every binary root parameter is zero or one. The negative simple root element
at one is `x n x`, where `x` is its positive root element and `n` the simple
Weyl word; `x` is an involution in characteristic two. Hence `U` and the four
simple Weyl words contain both existing split seeds, which generate the split
matrix group. This supplies the generation input for a split Bruhat proof;
it does not assert fixed-point generation or Bruhat coverage.

Source: Steinberg's Chevalley generators and rank-one relations, also GLS3
1.12.1 in `refs/KGroup/GLS3/Chapter1.tex`; the binary parabolic application is
Aschbacher–Smith F.1.12(I)(5), `refs/quasithin.pdf`, printed pp.263–264.
-/

public section
namespace ReeF4.Parabolics.Binary.FixedGeometry.BruhatCoverage
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open ReeF4.LargeLocalSeeds ReeF4.LocalBlockInput

noncomputable section

local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- The positive subgroup and four simple Weyl lifts generate the binary split group. -/
theorem splitUnipotent_sup_weyl_eq_top :
    splitUnipotent 0 ⊔ splitWeylSubgroup = ⊤ := by
  let H := splitUnipotent 0 ⊔ splitWeylSubgroup
  have hp (r : F4Chevalley.Root) (t : CoefficientField 0)
      (hr : typeF4RootPairing_base.IsPos r) : rootGeneratorInGroup 0 r t ∈ H :=
    mem_sup_left (subset_closure ⟨r, t, hr, rfl⟩)
  have hn (i : Fin 4) (t : CoefficientField 0) :
      rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) t ∈ H := by
    have ht : t = 0 ∨ t = 1 := by
      apply eq_zero_or_one_of_sq_eq_self
      simpa using field_pow 0 t
    rcases ht with rfl | rfl
    · have he : rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) 0 = 1 := by
        apply Subtype.ext
        exact F4Chevalley.rootCurve_zero _
      rw [he]
      exact H.one_mem
    · let x := rootGeneratorInGroup 0 (typeF4SimpleRootIndex i) 1
      have hx : x ∈ H := hp _ _
        (typeF4RootPairing_base.isPos_of_mem_support
          (typeF4RootPairing_baseEquiv i).property)
      have hxx : x * x = 1 := by
        apply Subtype.ext
        change F4Chevalley.rootCurve _ _ * F4Chevalley.rootCurve _ _ = 1
        rw [← F4Chevalley.rootCurve_add, CharTwo.add_self_eq_zero,
          F4Chevalley.rootCurve_zero]
      have hw : simpleWord 0 [i] ∈ H :=
        mem_sup_right (simpleWord_mem_splitWeylSubgroup [i])
      have he : x * simpleWord 0 [i] * x =
          rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) 1 := by
        change x * (weylWord 0 (typeF4SimpleRootIndex i) 1 * 1) * x = _
        simp only [mul_one, weylWord, inv_one, CharTwo.neg_eq]
        change x * (x * rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) 1 * x) * x = _
        calc
          _ = (x * x) * rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) 1 * (x * x) := by group
          _ = _ := by rw [hxx]; simp
      exact he ▸ H.mul_mem (H.mul_mem hx hw) hx
  have hs (s : Side) : splitSeed 0 s ≤ H := by
    apply (closure_le _).mpr
    rintro _ ⟨r, t, hr, rfl⟩
    rcases hr with hr | ⟨i, _, rfl⟩
    · exact hp r t hr
    · exact hn i t
  apply top_unique
  rw [← splitSeed_sup_eq_top 0]
  exact sup_le (hs .suzuki) (hs .linear)

end
end ReeF4.Parabolics.Binary.FixedGeometry.BruhatCoverage
