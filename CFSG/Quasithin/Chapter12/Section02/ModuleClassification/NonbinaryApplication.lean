module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.NonbinaryRecovery
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonbinaryNaturalInput
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternatives
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.SplitModels

/-!
# NonbinaryApplication

The three nonbinary action rows supply the existing Chapter11 input on the original chosen central quotient. Cover recovery proves its faithfulness; the retained source orbit branch supplies T-invariance without identifying the seed with its orbit by assumption.
Source: Aschbacher--Smith 11.0.1 and 12.2.2, pp.759--760,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {H : Type*} [Group H]
    {ρ : Representation (ZMod 2) H D.space} {K : Subgroup H}
    (c : D.LiteralComparison ρ K)
include c

/-- A literal nonbinary B.5 row: the central quotient action, with its marking. -/
inductive NonbinaryRow (s : MovedSection ρ K) (F : BinaryField) : Prop
  | linearThree (e : ActionEquiv (s.action.comp K.subtype) (linearNatural F 3))
  | symplectic (e : ActionEquiv (s.action.comp K.subtype) (binarySymplectic F))
  | g2 (e : ActionEquiv (s.action.comp K.subtype) (binaryG2 F))

/-- Construct exactly the existing Chapter11 input, including faithfulness of
the original two-core quotient action and the actual T-normalization. -/
theorem nonbinaryInput_of_source_branch
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (horbits : componentOrbit V (normalizer (L : Set G)) = V ∨
      (componentOrbit V (T : Subgroup G) = V ∧ V ⊓ centralizer (L : Set G) = ⊥))
    (hff : IsFFModule (normalizerRepresentation D.chosenAction))
    (s : MovedSection ρ K) (hf : Function.Injective (s.action.comp K.subtype))
    (F : BinaryField) (hF : 1 < F.degree) (row : NonbinaryRow s F) :
    Nonempty D.NonbinaryNaturalInput := by
  have hT := (D.structural_of_orbit_equalities_of_many h hmany horbits).1
  have hm : Function.Injective D.centralQuotientAction ∧ D.NaturalRankTwoAction F := by
    cases row with
    | linearThree e =>
      have hp := c.projection_injective_of_nonbinary_linearThree h.quasisimple F hF e.groupEquiv
      exact ⟨c.centralAction_injective s hf hp,.sl3 ⟨(c.quotientMarking s hp).trans e⟩⟩
    | symplectic e =>
      have hp := c.projection_injective_of_nonbinary_symplectic h.quasisimple F hF e.groupEquiv
      exact ⟨c.centralAction_injective s hf hp,.sp4 ⟨(c.quotientMarking s hp).trans e⟩⟩
    | g2 e =>
      have hp := c.projection_injective_of_nonbinary_g2 h.quasisimple F hF e.groupEquiv
      exact ⟨c.centralAction_injective s hf hp,.g2 ⟨(c.quotientMarking s hp).trans e⟩⟩
  exact ⟨⟨h,hmany,hT,hff,F,hF,hm.1,hm.2⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
