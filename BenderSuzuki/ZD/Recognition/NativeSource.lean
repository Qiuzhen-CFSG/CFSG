module

public import BenderSuzuki.ZD.Recognition.CoverReduction
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.NativeSource
public import BenderSuzuki.ZD.SimpleCorollary

/-!
# Theorem ZD

The double-cover Sylow-fixer theorem completes the minimal-simple reduction.
The residual argument then proves strong embedding in that simple reduction.
The existing strong-induction assembly and Theorem SE give every clause of
Theorem ZD for the original product-disconnected set and subgroup. In a
nonabelian simple group this identifies the original subgroup as a Borel.

Source: GLS IV, Chapter 2, Theorem ZD and Corollary ZD, with the proof in
Sections 3--17 and the covering input of Chapter 4, Lemma 2.8(b,c).
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory
universe u

/-- The genuine perfect-central-double-cover theorem supplies the universal
rigidity input used by the minimal-simple reduction. -/
public theorem doubleCoverSylowRigidity : DoubleCoverSylowRigidity.{u} := by
  intro E B _ _ _ _ hB f hcard P α hfix
  exact bender_cover_fixingSylow_eq_one hB f hcard P α hfix

/-- Every original minimal ZD counterexample has the complete simple
reduction, including its proper distinguished-closure embedding clauses. -/
public theorem MinimalCounterexample.simpleReduction
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) : SimpleReduction Z M :=
  h.simpleReduction_of_doubleCoverRigidity doubleCoverSylowRigidity

/-- The full finite-group product-disconnected theorem, with no additional
recognition, covering, rank, action or embedding premise. -/
public theorem theorem_ZD
    {G : Type u} [Group G] [Finite G] (Z : Set G) (M : Subgroup G)
    (h : IsProductDisconnected Z M) : Conclusion Z M :=
  conclusion_of_doubleCoverRigidity_and_embedding doubleCoverSylowRigidity
    (fun _ _ hm hr => stronglyEmbedded_of_minimalCounterexample hm hr) Z M h

/-- The simple Bender model and Borel assertions of Corollary ZD for the
original product-disconnected subgroup. -/
public theorem simple_bender_borel
    {G : Type u} [Group G] [Finite G] (Z : Set G) (M : Subgroup G)
    (h : IsProductDisconnected Z M) (hsimple : IsSimpleGroup G)
    (hna : ¬ IsMulCommutative G) :
    IsSimpleBenderGroup G ∧ IsBorelSubgroup M :=
  simple_bender_borel_of_conclusion Z M h hsimple hna (theorem_ZD Z M h)

end BenderSuzuki.ZD
