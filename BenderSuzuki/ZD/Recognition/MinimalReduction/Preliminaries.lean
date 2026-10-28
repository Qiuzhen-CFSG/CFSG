module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Preliminaries.Elementary
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Preliminaries.Generation
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Preliminaries.Counting

/-!
# Preliminary reduction of a minimal counterexample to Theorem ZD

In a minimal counterexample the distinguished involutions generate the group,
form a single conjugacy class, and are 2-central. The distinguished subgroup
contains an ambient Sylow 2-subgroup and controls fusion on that subgroup.

Generation follows by transporting every clause of `Conclusion` from the
generated subgroup and applying minimality. The odd-product argument gives
conjugacy; counting gives odd cardinality of `Z ∩ M`, hence a fixed point for
a Sylow action. This proves 2-centrality, which supplies fusion control by
correcting conjugators in a centralizer. All counting and transport premises
are discharged here.

Source: GLS, Volume 4, Chapter 2, (3B), Lemma 3.3(a), Proposition 3.6(e),
and Lemmas 4.1 and 4.2(a); `refs/KGroup/GLS4/Chapter2.tex`.
-/

namespace BenderSuzuki.ZD

variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- GLS Lemma 3.3(a): the distinguished involutions form one conjugacy class. -/
public theorem MinimalCounterexample.one_class (h : MinimalCounterexample Z M) :
    ∀ x ∈ Z, ∀ z ∈ Z, IsConj x z :=
  productDisconnected_isConj h.disconnected

/-- GLS Lemma 4.1: every distinguished involution is central in an ambient
Sylow 2-subgroup. Odd cardinality is supplied by the counting argument. -/
public theorem MinimalCounterexample.two_central (h : MinimalCounterexample Z M) :
    ∀ z ∈ Z, ∃ S : Sylow 2 G, z ∈ S ∧ ∀ s : S, Commute z (s : G) :=
  two_central_of_odd_card h.disconnected (productDisconnected_odd_card h.disconnected)

/-- GLS Lemma 4.2(a) on an ambient Sylow subgroup contained in `M`. -/
public theorem MinimalCounterexample.fusion (h : MinimalCounterexample Z M) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ M ∧ ControlsFusionIn M (S : Subgroup G) :=
  productDisconnected_fusion_of_two_central h.disconnected h.two_central

/-- The generation, conjugacy, 2-centrality and fusion conclusions needed
for the minimal-counterexample simple reduction. -/
public theorem MinimalCounterexample.preliminaries (h : MinimalCounterexample Z M) :
    Subgroup.closure Z = ⊤ ∧
    (∀ x ∈ Z, ∀ z ∈ Z, IsConj x z) ∧
    (∀ z ∈ Z, ∃ S : Sylow 2 G, z ∈ S ∧ ∀ s : S, Commute z (s : G)) ∧
    (∃ S : Sylow 2 G, (S : Subgroup G) ≤ M ∧ ControlsFusionIn M (S : Subgroup G)) :=
  ⟨h.closure_eq_top, h.one_class, h.two_central, h.fusion⟩

end BenderSuzuki.ZD
