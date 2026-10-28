module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.Contracts
public import Theory.GroupTheory.MaximalSylowAutomorphisms

/-!
# The actor-wise alternative for the J₄ pair sieve

The source needs a proper nonzero invariant subgroup of the complement's
Frattini quotient for each acting two-group. A sufficient reduction either
constructs that subgroup directly or supplies compatible actions on an
actual max4-type overgroup. The second branch is exactly the conclusion of
`MaximalFourPairActions`, including every actor and the equality on R.

The new reduction is a separate, unproved interface. It does not assert
universal placement and does not assume irreducibility in `PairInput`.
The local-model inputs below retain all ambient pair hypotheses. They ask
only for the max1 and max2 calculations after compatible local actions
have been constructed; those calculations remain separate obligations.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`); see `docs/quasithin-proof-basis.md`.
-/

set_option backward.isDefEq.respectTransparency true

@[expose] public section

open Subgroup
open Janko4.LocalStructure.SymmetricLinear

attribute [local irreducible] Janko4.modelGroup max4Subgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- A proper nonzero subgroup invariant under every member of the given actor. -/
def ActorReducible {H : Type*} [Group H] (D : Subgroup (MulAut H)) : Prop :=
  ∃ A : Subgroup (H ⧸ frattini H), A ≠ ⊥ ∧ A ≠ ⊤ ∧
    ∀ a ∈ D, ∀ x ∈ A, quotientAut (frattini H) a x ∈ A

/-- The complete placement branch, with the overgroup allowed to depend on D. -/
def CompatibleMaximalFour (S R : Subgroup Janko4.Model)
    (D : Subgroup (MulAut R)) : Prop :=
  ∃ (M : Subgroup Janko4.Model) (hRM : R ≤ M),
    S ≤ M ∧ Nonempty (M ≃* max4Subgroup) ∧
      ∀ a ∈ D, ∃ c : MulAut M,
        ∀ r : R, inclusion hRM (a r) = c (inclusion hRM r)

/-- The sufficient actor-wise alternative, separate from universal placement.
Its unconditional proof is required before completing the J₄ action sieve. -/
def AdequateMaximalFourPairActions : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model) (R : Subgroup Janko4.Model), PairInput S R →
    ∀ D : Subgroup (MulAut R), D ≤ pairAutomizer S.toSubgroup R → IsPGroup 2 D →
      ActorReducible D ∨ CompatibleMaximalFour S.toSubgroup R D

namespace Adequate

/-- Local lifts preserve the supplied Sylow as well as agreeing on R. The
Sylow clause is needed for subsequent quotient pair-action transport. -/
def CompatibleSylowActions {G : Type*} [Group G] (S R M : Subgroup G)
    (hRM : R ≤ M) (D : Subgroup (MulAut R)) : Prop :=
  ∀ a ∈ D, ∃ c : MulAut M,
    (∀ x : M, (c x : G) ∈ S ↔ (x : G) ∈ S) ∧
      ∀ r : R, inclusion hRM (a r) = c (inclusion hRM r)

/-- The remaining calculation for one concrete local model. All original
ambient hypotheses are available, and no invariant subgroup is a premise. -/
def LocalModelPairReducibility (L : Type*) [Group L] : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model) (R : Subgroup Janko4.Model), PairInput S R →
    ∀ (M : Subgroup Janko4.Model), IsCoatom M →
    ∀ (_hSM : S.toSubgroup ≤ M) (hRM : R ≤ M), (M ≃* L) →
    ∀ D : Subgroup (MulAut R), D ≤ pairAutomizer S.toSubgroup R → IsPGroup 2 D →
      CompatibleSylowActions S.toSubgroup R M hRM D → ActorReducible D

/-- Stability under every Sylow-preserving ambient automorphism constructs
all the local lifts, retaining their Sylow action and equality on R. -/
theorem compatibleSylowActions_of_stable
    {G : Type*} [Group G] (S R M : Subgroup G) (hRM : R ≤ M)
    (D : Subgroup (MulAut R)) (hD : D ≤ pairAutomizer S R)
    (hstable : ∀ b : MulAut G, (∀ x, b x ∈ S ↔ x ∈ S) →
      ∀ x, b x ∈ M ↔ x ∈ M) : CompatibleSylowActions S R M hRM D := by
  intro a ha
  obtain ⟨b, hb, he⟩ := hD ha
  refine ⟨stableAut M b (hstable b hb), ?_, ?_⟩
  · intro x
    rw [stableAut_coe]
    exact hb x
  · intro r
    apply Subtype.ext
    rw [stableAut_coe]
    exact he r

end Adequate
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
