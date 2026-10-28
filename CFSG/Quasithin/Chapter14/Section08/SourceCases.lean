module

public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.MaximalCounterexample
public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.StarPlacement

/-!
# The five local quotient branches in the final Theorem D reduction

Failure of D supplies a maximal actual Chapter 13 counterexample. The genuine
13.3.2 catalogue splits its literal quotient L/O₂(L) into five rows. The
13.3.16 exclusion removes U₃(3), and 13.8.1 removes both A₆ rows using the
counterexample's Sp₆(2) and U₄(3) exclusions. In the L₃(2) row, the earlier
12.2.2 and 13.3.2 implications construct a chosen natural module and its
invariant flag. Splitting the actual U = ⟨V^{N_G(V₁)}⟩ into abelian and
nonabelian cases applies 14.7.75 and 14.4.14 respectively.

Only the A₅ row remains. The narrower source 13.6.1 output gives D; the full
Main-Theorem output of the current A₅ terminal argument instead gives a
separate implication to `IsQTKEModel`. No reverse catalogue inclusion is used.

The multiple-overgroup guard available in MainForward is retained throughout,
so the earlier guarded source applications need no stronger universal variant.
All earlier source implications are explicit parameters. These are conditional
assembly theorems, not proofs of those inputs or an unconditional Theorem D.
The six recognition contracts below concern actual quotients, modules, flags
and model isomorphisms. Source: Aschbacher--Smith 14.8.1--2, printed pp.1078--1079.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter14.Section08.SourceCases

open Subgroup Theory.GroupTheory ClassificationModels
open Chapter1.Section02.LocalModels
open Chapter12.Section02 Chapter12.Section08
open Chapter13.Section03.Noncentrality.SupercriticalSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u
variable (G : Type u) [Group G] [Finite G]

/-- The genuine 13.3.2(1--2) implication on a standing source counterexample.
Its conclusion classifies every actual faithful local component. -/
def Catalogue : Prop :=
  ∀ (T : Sylow 2 G) (L : Subgroup G),
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
    Counterexample T L → Source1332OneTwo T

/-- The U₃(3) quotient exclusion of 13.3.16 on the original local subgroup. -/
def UnitaryExclusion : Prop :=
  ∀ (T : Sylow 2 G) (L : Subgroup G),
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard → Counterexample T L →
    ¬ ClassicalGroup.IsPSU (L ⧸ pCore 2 L) 3 3

/-- The two A₆ quotient rows of 13.8.1. Maximal choice is supplied by the
dispatcher and is available to the ordinary natural-six source arguments. -/
def SixRecognition : Prop :=
  ∀ (T : Sylow 2 G) (L : Subgroup G),
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
    Maximal (Counterexample T) L →
    (IsAlternating (L ⧸ pCore 2 L) 6 ∨ IsAlternatingCover (L ⧸ pCore 2 L) 6) →
      ClassicalGroup.IsPSp G 3 2 ∨ ClassicalGroup.IsPSU G 4 3

/-- The D-specific nonabelian alternative of 14.4.14, on the actual natural
module and flag of Hypothesis 12.8.1(1). -/
def NonabelianRecognition : Prop :=
  ∀ (T : Sylow 2 G) (L V : Subgroup G),
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard → Counterexample T L →
    HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3 →
    ∀ F : InvariantFlag T V 3, ¬ IsMulCommutative F.U →
      IsG2At G 3 ∨ Nonempty (G ≃* KnownSimple.SporadicName.hs.Carrier)

/-- The D-specific abelian alternative of 14.7.75, on the same literal span
as the nonabelian branch. -/
def AbelianRecognition : Prop :=
  ∀ (T : Sylow 2 G) (L V : Subgroup G),
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard → Counterexample T L →
    HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3 →
    ∀ F : InvariantFlag T V 3, IsMulCommutative F.U →
      Nonempty (G ≃* KnownSimple.SporadicName.ru.Carrier)

/-- The sufficient A₅ input for the full Main Theorem. The current terminal
source export has this full-model conclusion, including field-two endpoints. -/
def FiveRecognition : Prop :=
  ∀ (T : Sylow 2 G) (L : Subgroup G),
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
    Maximal (Counterexample T) L →
    IsAlternating (L ⧸ pCore 2 L) 5 → IsQTKEModel G

variable {G}
variable (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
  (caseOne : Section03.CaseOneSource.Earlier1332CaseOne.{u})
  (catalogue : Catalogue G) (unitary : UnitaryExclusion G)
  (six : SixRecognition G) (nonabelian : NonabelianRecognition G)
  (abelian : AbelianRecognition G)

include structural caseOne nonabelian abelian

/-- The L₃(2) branch constructs its original module and flag before splitting
the conjugate span. No flag, abelianness or local identification is assumed. -/
theorem theoremDModel_of_linearThree {T : Sylow 2 G} {L : Subgroup G}
    (d : Counterexample T L) (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    IsTheoremDModel G := by
  classical
  obtain ⟨V, ⟨s⟩⟩ := Section03.CaseOneSource.exists_higherRankHypothesis
    d caseOne structural hq
  obtain ⟨_, F, _⟩ := s.exists_flag_geometry structural
  by_cases hU : IsMulCommutative F.U
  · exact .exceptional (.sporadic .ru (by simp) (abelian T L V hmany d s F hU))
  · rcases nonabelian T L V hmany d s F hU with hG2 | hHS
    · exact .exceptional (.g2_three hG2)
    · exact .exceptional (.sporadic .hs (by simp) hHS)

include catalogue unitary six

/-- The five-row source split leaves only the actual A₅ counterexample.
The catalogue is applied to the selected member of the faithful family. -/
theorem theoremDModel_or_five_counterexample
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty) :
    IsTheoremDModel G ∨ ∃ L : Subgroup G,
      Maximal (Counterexample T) L ∧ IsAlternating (L ⧸ pCore 2 L) 5 := by
  classical
  by_cases hD : IsTheoremDModel G
  · exact Or.inl hD
  obtain ⟨L, hmax⟩ :=
    LieTypeBranch.exists_maximal_counterexample_of_not_theoremDModel h T hne hD
  have d := hmax.1
  have hm : MidSizeModel (L ⧸ pCore 2 L) := (catalogue T L hmany d L d.local_component).2
  rcases hm with h5 | h3 | h6 | hc6 | hu
  · exact Or.inr ⟨L, hmax, h5⟩
  · exact Or.inl (theoremDModel_of_linearThree structural caseOne nonabelian abelian d h3 hmany)
  · rcases six T L hmany hmax (Or.inl h6) with hs | hu
    · exact (d.no_symplectic_six hs).elim
    · exact (d.no_unitary_four hu).elim
  · rcases six T L hmany hmax (Or.inr hc6) with hs | hu
    · exact (d.no_symplectic_six hs).elim
    · exact (d.no_unitary_four hu).elim
  · exact (unitary T L hmany d hu).elim

/-- The original D conclusion in the multiple-overgroup case follows if the A₅
producer supplies its precise
13.6.1 pair of models. This preserves the stricter standalone D catalogue. -/
theorem theoremDModel_of_source_branches
    (five : ∀ (T : Sylow 2 G) (L : Subgroup G),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Maximal (Counterexample T) L →
      IsAlternating (L ⧸ pCore 2 L) 5 →
        ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3)
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty) : IsTheoremDModel G := by
  rcases theoremDModel_or_five_counterexample structural caseOne catalogue unitary
    six nonabelian abelian h T hmany hne with hD | ⟨L, hmax, h5⟩
  · exact hD
  · rcases five T L hmany hmax h5 with hu | hl
    · exact .exceptional (.unitary_binary hu)
    · exact .exceptional (.linear_three hl)

/-- The shorter sufficient route for MainForward uses the existing full-model
A₅ endpoint directly. It does not claim the narrower Theorem D conclusion. -/
theorem qtkeModel_of_source_branches (five : FiveRecognition G)
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty) : IsQTKEModel G := by
  rcases theoremDModel_or_five_counterexample structural caseOne catalogue unitary
    six nonabelian abelian h T hmany hne with hD | ⟨L, hmax, h5⟩
  · exact hD.toQTKEModel
  · exact five T L hmany hmax h5

end CFSG.Quasithin.Chapter14.Section08.SourceCases
