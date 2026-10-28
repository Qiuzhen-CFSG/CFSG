module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.SuzukiMoved
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.OddJankoExclusion
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.LinearThree.Source

/-!
# The remaining original central Hall configurations

The literal Hall subgroup is a three-group in the linear-three row. The
odd-prime and Janko rows are excluded; a separated binary SL2 seed gives
the required exponent. In the Suzuki row, any starred actor moving the
original component constructs moved minimality and gives that exponent.

The remaining alternatives record the nonseparated seed with both original
component restrictions, or a Suzuki quotient with every starred actor in
the exact quotient-action kernel and a three-divisible component orbit
moved there. These are residual configurations, not source hypotheses or
proofs of SourceNonnormalCentralHallAt. Their exclusion and final assembly
remain with this source owner.
Source: Aschbacher--Smith 10.1.1--2 and10.2.3, printed pp.741--742,745.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance remainingCasesElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The unchanged nonseparated even-linear seed with its actual component
marking, full quotient kernel, and constituent/tensor alternative. -/
def OriginalNonseparatedEvenCase : Prop :=
  ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
    ∃ n : ℕ, 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
      ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
        D.seed ≤ centralizer (L : Set G)) ∧ OriginalEvenNaturalAnalysis D ht n e

/-- The residual Suzuki configuration includes its original quotient
isomorphism, all starred actors, and a genuine moved component in their
literal component-action kernel. -/
def OriginalSuzukiCentralizingSupport
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) : Prop :=
  (∃ m : ℕ, 0 < m ∧ Nonempty ((L ⧸ pCore 2 L) ≃*
    BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∧
  (∀ A : Subgroup (actionImage (movedStabilizerAction D)),
    A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)) →
    A ≤ (originalMovedQuotientAction D hn).ker) ∧
  ∃ A J : Subgroup (actionImage (movedStabilizerAction D)),
    A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)) ∧
    IsComponent _ J ∧ 3 ∣ Nat.card J ∧
    J ≤ (originalMovedQuotientAction D hn).ker ∧
    componentOrbit J A ≤ (originalMovedQuotientAction D hn).ker ∧
    componentOrbit J A ≠ ⊥ ∧ ⁅componentOrbit J A,A⁆ = componentOrbit J A

/-- The exact original Hall consumer has its required numerical conclusion
or one of the two explicit remaining module configurations. Every earlier
catalogue, constituent and actor-movement premise has been discharged. -/
theorem original_hall_conclusion_or_remaining_cases
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      OriginalNonseparatedEvenCase D ∨ OriginalSuzukiCentralizingSupport D c.nonnormal := by
  by_cases he : Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
  · exact Or.inl (Or.inl (isThreeGroup_of_image D B c.hall_le c.faithful
      (source_linearThreeImageAt T L D H B c he)))
  rcases hall_exponent_or_original_even_analysis_or_suzuki D c he with hh | hc | ⟨m,hm,⟨e⟩⟩
  · exact Or.inl (Or.inr ⟨hh.choose,hh.choose_spec.2⟩)
  · exact Or.inr (Or.inl hc)
  · rcases hall_exponent_or_suzuki_centralizing_component_support D c he m hm e with hh | hs
    · exact Or.inl (Or.inr ⟨hh.choose,hh.choose_spec.2⟩)
    · exact Or.inr (Or.inr ⟨⟨m,hm,⟨e⟩⟩,hs⟩)
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
