module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification
/-!
# Complete source reduction of B.4.2 to three exceptional families

Every constructor of the genuine full Theorem C catalogue is dispatched using
its proved original-action module classification. The result retains precisely
the triality, Ree F4 and sporadic quotient alternatives whose FF exclusions
have independent source producers. No representation recognition or model row
is an assumption. The last theorem applies the reduction to the literal B.4.2
best offender, using genuine earlier A and C.

Source: Aschbacher–Smith B.4.2, printed p.86, and A.2.4.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

inductive RemainingModel (S : Type*) [Group S] : Prop
  | triality (n : ℕ) (hn : 0<n) (model : Triality.Standard.IsTrialityGroupAt (2^n) S)
  | ree (m : ℕ) (hm : 1≤m) (model : Nonempty (S ≃* ReeF4.Model m))
  | sporadic (model : ChapterA.Section02.IsTheoremCSporadicModel S)

theorem case_or_remaining_model (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hff : IsFFModule ρ) (hm : ChapterA.Section02.IsTheoremCModel (L ⧸ center L)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) ∨
      RemainingModel (L ⧸ center L) := by
  obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
  cases hm with
  | alternating n hn e => exact Or.inl (alternating_case h hff hn (Classical.choice e))
  | odd hm => exact Or.inl (odd_case h hff hm)
  | bender hm => exact Or.inl (bender_case h hff hm)
  | linear_binary n hn hm => exact Or.inl (binary_linear_case h hn hm)
  | sporadic hm => exact Or.inr (.sporadic hm)
  | rank_two n hm =>
    cases hm with
    | linear hn hm =>
      exact Or.inl (ChapterK.Linear.SourceFF.actionCase_of_bestOffender ρ h.sqtk h.fitting.symm
        h.quasisimple h.faithful h.irreducible n hn hm A hA)
    | symplectic hn hm => exact Or.inl (symplectic_model_case h hff hn hm)
    | g2 hn hm => exact Or.inl (g2_model_case h hff hn hm)
    | triality hn hm => exact Or.inr (.triality n hn hm)
    | ree_f4 m hm _ he => exact Or.inr (.ree m hm he)
    | symplectic_derived _ he => exact Or.inl (binary_symplectic_derived_case h hff (Classical.choice he))
    | g2_derived _ he => exact Or.inl (g2_binary_case h hff (Classical.choice he))
    | tits _ he => exact (tits_exclusion h (Classical.choice he)).elim

theorem case_or_remaining_of_theoremsAC
    (hA : ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple G)
    (hC : ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple (L ⧸ center L))
    (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hbest : IsBestOffender ρ A) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) ∨
      RemainingModel (L ⧸ center L) := by
  let h := source_hypotheses_of_bestOffender hsq hfit hL hf hi hbest
  exact case_or_remaining_model h ⟨A,hbest.isOffender ρ⟩
    (quotient_model_of_theoremsAC hA hC h)

end CFSG.Quasithin.ChapterB.SourceClassification
