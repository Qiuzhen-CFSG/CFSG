module

public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import Theory.GroupAction.PerfectCentralQuotientSylow
public import Mathlib.GroupTheory.GroupExtension.Defs

/-!
# Conventions for the odd-characteristic and sporadic preliminary cases

The input alternatives are exactly (E2)(ii)–(iii), printed p.1170 of
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
of 1 March 2004. Centralizers for covering groups in 16.1.5 are fixed subgroups
of the action on L/Z(L), rather than images of fixed subgroups upstairs.
Extension descriptions can use `GroupExtension N E Q`, which specifies a short
exact sequence and supplies no splitting.

The innerness property below is the conclusion needed for these alternatives
in 16.1.6. It includes arbitrary two-elements and the identity. It is not the
conclusion for all even-type components: the characteristic-two A₆ case retains
the source's S₆ exception. The transfer theorem only lifts a proved model
property; it does not assert the unproved family calculations.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.OtherPreliminaries

open Subgroup Theory.GroupTheory

/-- The actual full groups in (E2)(ii), or the actual quotient in (E2)(iii). -/
def IsOtherEvenTypeComponent (L : Type*) [Group L] : Prop :=
  ClassicalGroup.IsPSL L 3 3 ∨
    (∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p) ∨
    IsEvenTypeSporadicQuotient (L ⧸ pCore 2 L)

/-- The source's C_{L/Z(L)}(r), using the genuine induced automorphism. -/
abbrev QuotientCentralizer {L : Type*} [Group L] (r : MulAut L) :
    Subgroup (L ⧸ center L) := ((center L).quotientAut r).fixedSubgroup

/-- Innerness for every two-element fixing a Sylow two-subgroup pointwise.
This is an obligation for each family, not an assumption in the source setup. -/
def HasInnerSylowCentralizingTwoAutomorphisms (L : Type*) [Group L] : Prop :=
  ∀ (r : MulAut L) (n : ℕ) (S : Sylow 2 L), r ^ (2 ^ n) = 1 →
    (∀ x ∈ S, r x = x) → ∃ g : L, r = MulAut.conj g

/-- The model calculation lifts to a perfect central cover without replacing
an arbitrary two-element by an involution. -/
theorem HasInnerSylowCentralizingTwoAutomorphisms.of_central_quotient
    {L M : Type*} [Group L] [Group M] [Finite L] [Finite M] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* M) (h : HasInnerSylowCentralizingTwoAutomorphisms M) :
    HasInnerSylowCentralizingTwoAutomorphisms L := by
  intro r n S hr hS
  obtain ⟨T, hT⟩ := MulAut.centralQuotientAction_exists_fixed_sylow e r S hS
  apply (MulAut.centralQuotientAction_inner_iff e r).mp
  apply h (MulAut.centralQuotientAction e r) n T _ hT
  rw [← map_pow, hr, map_one]

end CFSG.Quasithin.Chapter16.OtherPreliminaries
