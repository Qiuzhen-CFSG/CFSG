module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24Pair
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodePair

/-!
# Original M24 code pair degrees

Construct the pair inside the original H-star using the original chosen orbit,
component quotient and full automizer marking. The source torus calculation
excludes degree two without changing that orbit or any covering kernel.
The geometric degree is therefore one or three. The remaining source
generation comparison, local normalizer construction and code exclusion are
not assumed or asserted by this application.

Source: Aschbacher--Smith 8.2.2--3 and H.16.6--7,
printed pp.714--716,404--405, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open Chapter8.Section02.HermitianSource

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual selected pair of the original M24 code has degree one or three.
No pair, positive weak-closure parameter or generation divisibility is assumed. -/
theorem sourceOrbit_m24_code_pair_one_or_three_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I),
      GeometricSelected H T (normalizer (L : Set G)) D.sourceOrbit I k i S ∧
      (k = 1 ∨ k = 3) := by
  obtain ⟨I,k,i,S,s⟩ := D.sourceOrbit_m24_geometric_pair_of_many h hmany hV hq hnon hH
  exact ⟨I,k,i,S,s,s.m24_code_parameter_one_or_three a E hE⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
