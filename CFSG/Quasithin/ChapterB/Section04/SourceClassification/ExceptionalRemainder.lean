module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Remaining
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Sporadic

/-!
# The two remaining exceptional families in the genuine B.4.2 source reduction

The complete sporadic FF exclusion removes the last non-Lie alternative from
the full Theorem C dispatcher. The actual faithful irreducible action therefore
has a proved B.4.2 row, or its central quotient is a binary triality group or
a nonsmall Ree F4 group. Those two original-hypothesis FF exclusions remain
independent source obligations. The older three-family interface is preserved.

Source: Aschbacher--Smith B.4.2, printed p.86, and K.4, p.457.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

inductive RemainingExceptionalModel (S : Type*) [Group S] : Prop
  | triality (n : ℕ) (hn : 0<n) (model : Triality.Standard.IsTrialityGroupAt (2^n) S)
  | ree (m : ℕ) (hm : 1≤m) (model : Nonempty (S ≃* ReeF4.Model m))

/-- All source families other than triality and Ree F4 are classified. -/
theorem case_or_remaining_exceptional (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hff : IsFFModule ρ) (hm : ChapterA.Section02.IsTheoremCModel (L ⧸ center L)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) ∨
      RemainingExceptionalModel (L ⧸ center L) := by
  rcases case_or_remaining_model h hff hm with hc | hm
  · exact Or.inl hc
  · cases hm with
    | triality n hn hm => exact Or.inr (.triality n hn hm)
    | ree m hm he => exact Or.inr (.ree m hm he)
    | sporadic hm => exact (sporadic_false h hff hm).elim

/-- The two-family reduction on the original B.4.2 best-offender domain. -/
theorem case_or_exceptional_of_theoremsAC
    (hA : ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple G)
    (hC : ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple (L ⧸ center L))
    (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hbest : IsBestOffender ρ A) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) ∨
      RemainingExceptionalModel (L ⧸ center L) := by
  let h := source_hypotheses_of_bestOffender hsq hfit hL hf hi hbest
  exact case_or_remaining_exceptional h ⟨A,hbest.isOffender ρ⟩
    (quotient_model_of_theoremsAC hA hC h)

end CFSG.Quasithin.ChapterB.SourceClassification
