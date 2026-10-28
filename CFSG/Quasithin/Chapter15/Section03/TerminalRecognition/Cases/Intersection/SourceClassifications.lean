module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.Source
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape

/-!
# Source-facing FF witnesses for the terminal intersection

The full corrected B.5.6 witness uses the projective-line convention of
K.1.3: its triple-six offender fixes a two-dimensional F₄ vector subspace.
The alternative group configuration retains the actual A₆ and C₃ subgroups,
their product map and the prescribed outer element, without requiring the
disputed module splitting in B.5.6(4). Every other branch retains the full
source action conclusion. These are classification inputs, not a proof of
B.5.6 or a reduced list containing the terminal intersection.

The application below proves applicability on the same offender subgroup
and the same restriction of `quotientAction`. Both row-comparison owners
can use this input independently; their assembly must discharge all rows.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1/B.5.6,
printed pp.99–105; K.1.3, p.453; final proof of 15.3.1, p.1155. See also
the two source-interface corrections in `docs/quasithin-proof-basis.md`.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

universe u v

/-- The full projective-line classification, with the source outer group
configuration sufficient in place of the disputed splitting assertion. -/
def SourceFFAlternative {D : Type u} [Group D] {W : Type v}
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W) : Prop :=
  FFAlternatives.ProjectiveLine.SourceAlternative ρ ∨
    Nonempty (ChapterB.OuterSixThreeShape D)

/-- A sufficient universal source input. Proving it remains with the B.5.6
owner; it assumes no terminal image model or Thompson residual identity. -/
def SourceFFClassificationInput (K : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D]
    (W : Type v) [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W),
    FFHypothesis K ρ → SourceFFAlternative ρ

namespace SourceInput
variable {H : Type u} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- Apply the source-facing classifier to the original offender action;
all B.5.3 applicability premises come from the genuine local source input. -/
theorem full_sourceFF_alternative {K : GroupClass.{u}} (hH : IsSQTK K H)
    (classification : SourceFFClassificationInput.{u,u} K) :
    SourceFFAlternative d.offenderAction :=
  classification _ _ _ (d.offender_hypothesis hH)

/-- The full corrected source implication also specializes directly,
without imposing any legacy triple-six offender clause. -/
theorem full_projectiveLine_alternative {K : GroupClass.{u}} (hH : IsSQTK K H)
    (classification : FFAlternatives.ProjectiveLine.CompleteClassificationInput.{u,u} K) :
    SourceFFAlternative d.offenderAction :=
  Or.inl (classification.general _ _ _ (d.offender_hypothesis hH))

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
