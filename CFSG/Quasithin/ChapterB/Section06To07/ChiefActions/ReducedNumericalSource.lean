module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.NumericalSource
import all CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.NumericalSource

/-!
# No strong offenders on a reduced minimal parabolic

The original B.6.9 argument applies to the whole faithful binary module;
irreducibility is unnecessary when the two-core is explicitly trivial.
The solvable case is Glauberman's source theorem. The nonsolvable cases
use the proved natural-factor classification and its whole-module budgets.
The actual SQTK cover is retained, with no quotient-closure assertion.

The deliberate `import all` reuses the private numerical case proofs from
NumericalSource without changing that module's public boundary.
Source: Aschbacher--Smith B.6.9(1), printed pp.115--116. The original
12.9.5 point-centralizer multiplicity action is the consumer.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open SourceInduction QuasisimpleSource
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- B.6.9(1) on the whole faithful module, with its original SQTK cover. -/
theorem reduced_minimalParabolic_not_strong
    (hc : Nonempty (SQTKQuotient KnownSimple.IsKnownSimple H))
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (hcore : pCore 2 H = ⊥) (ρ : Representation (ZMod 2) H W)
    (hf : Function.Injective ρ) : ¬ IsStrongFFModule ρ := by
  intro hs
  have hff : IsFFModule ρ := by
    obtain ⟨A,hA⟩ := hs
    exact ⟨A,hA.1,hA.2.le⟩
  by_cases hsol : Group.IsSolvable H
  · obtain ⟨A,hA⟩ := hs
    exact (Glauberman.numerical_conclusions hsol hcore hf hff).2 A hA
  · have hsrc := nonsolvable_offender_natural_source ρ T hP hsol hf hff hcore hc
    rcases hsrc with ⟨hqs,⟨c,_⟩⟩ | ⟨d,hd₁,hd₂⟩
    · exact (section_not_strong ρ T hP hff hcore hqs c) hs
    · obtain ⟨_,_,_,hmodel⟩ := source_offender_two_factor_shared_natural ρ T hP hff hcore d
      rcases hmodel with ⟨F,⟨c⟩⟩ | ⟨c⟩
      · exact (pair_not_strong ρ _ F c) hs
      · obtain ⟨c⟩ := c
        exact (SourceTwoFactorCase.MarkedProduct.symmetric_not_strong ρ _ c) hs
end CFSG.Quasithin.ChapterB
