module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Preliminaries
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.OddContainment
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.OddLifting
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.SimpleBranch
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Simplicity

/-!
# The minimal ZD reduction from double-cover Sylow rigidity

Odd-core containment, genuine quotient descent and full conclusion lifting
exclude the odd core of a minimal counterexample without a covering input.
A nontrivial solvable normal subgroup then supplies a central subgroup A of
order two. The actual quotient G/A satisfies the structural ZD alternative.
Its derived Bender factor has a perfect central lift; double-cover rigidity
makes that lift simple. The proved reconstruction gives the full conclusion
upstairs, contradicting minimality.

The local-embedding and simplicity theorems now assemble every field of
SimpleReduction. The only remaining input is the precise Sylow-fixer theorem
for perfect central double covers of simple Bender groups. It is an explicit
mathematical premise, not an asserted model fact or source classification.

Source: GLS, Volume 4, Chapter 2, Lemma 4.5 and Propositions 4.3--4.4,
printed pp.34--39; the covering input is Chapter 4, Lemma 2.8(b,c).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII
universe u

/-- The remaining Bender-cover input: an automorphism fixing the actual
Sylow two-subgroup pointwise is trivial for a perfect central double cover. -/
@[expose] public def DoubleCoverSylowRigidity : Prop :=
  ∀ (E B : Type u) [Group E] [Finite E] [Group B] [Finite B],
    IsSimpleBenderGroup B → ∀ f : PerfectCentralCovering.Cover E B,
      Nat.card f.toMonoidHom.ker = 2 → ∀ (P : Sylow 2 E) (α : MulAut E),
        (∀ x : P, α (x : E) = x) → α = 1

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The first paragraph of GLS Lemma 4.5, with all quotient descent and
lifting premises supplied. No covering-group input is needed. -/
public theorem MinimalCounterexample.oddCore_eq_bot
    (h : MinimalCounterexample Z M) : pPrimeCore 2 G = ⊥ := by
  by_contra hne
  have hOM := h.oddCore_le h.closure_eq_top h.one_class h.two_central
  obtain ⟨S, hSM, hf⟩ := h.fusion
  have hq := productDisconnected_quotient_of_odd h.disconnected S hSM hf
    (pPrimeCore 2 G) hOM (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2)))
  exact h.fails (conclusion_of_oddCore_quotient h.disconnected h.closure_eq_top hOM
    (h.conclusion_quotient _ hne hq))

/-- GLS Lemma 4.5 from the precise double-cover rigidity theorem. The
central quotient, its covering component and the original distinguished
involution action are constructed by the proved source reductions. -/
public theorem MinimalCounterexample.solvable_normal_eq_bot_of_doubleCoverRigidity
    (h : MinimalCounterexample Z M) (rigidity : DoubleCoverSylowRigidity.{u})
    (N : Subgroup G) (hN : N.Normal) (hsol : Group.IsSolvable N) : N = ⊥ := by
  apply solvable_normal_eq_bot_of_core_and_central_exclusion
    h.closure_eq_top h.two_central h.oddCore_eq_bot _ N hN hsol
  intro A hAn hAc hAcard
  let : A.Normal := hAn
  have hAp : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by simpa using hAcard)
  have hAne : A ≠ ⊥ := by
    intro hbot
    norm_num [hbot] at hAcard
  have hs := h.central_quotient_structure h.closure_eq_top h.two_central h.fusion
    h.oddCore_eq_bot A hAc hAp hAne
  have hD := central_quotient_derived_model h.closure_eq_top h.oddCore_eq_bot
    A hAc hAcard hs
  have hK := central_quotient_component_simple_of_rigidity h.disconnected h.closure_eq_top
    h.two_central h.oddCore_eq_bot A hAc hAcard hs (by
      intro hcard P α hfix
      exact rigidity _ _ hD
        (centralLiftCover (QuotientGroup.mk' A) (QuotientGroup.mk'_surjective A)
          (by simpa only [QuotientGroup.ker_mk'] using hAc) (commutator (G ⧸ A)) hD)
        hcard P α hfix)
  exact h.fails (Or.inr (central_quotient_structure_of_simple_cover h.disconnected
    h.closure_eq_top h.one_class h.oddCore_eq_bot A hAc hAcard hs hK))

/-- All clauses of the minimal-counterexample simple reduction, including
strong embedding in each proper distinguished closure, from the single
remaining covering-group theorem. -/
public theorem MinimalCounterexample.simpleReduction_of_doubleCoverRigidity
    (h : MinimalCounterexample Z M) (rigidity : DoubleCoverSylowRigidity.{u}) :
    SimpleReduction Z M := by
  have hsol := h.solvable_normal_eq_bot_of_doubleCoverRigidity rigidity
  have hlocal := h.local_embedding_of_no_solvable_normal hsol
  exact ⟨isSimple_of_preliminary_and_local h h.closure_eq_top h.one_class
    h.two_central h.fusion hsol hlocal,
    h.closure_eq_top, h.one_class, h.two_central, h.fusion, hlocal⟩

end BenderSuzuki.ZD
