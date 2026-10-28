module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.Setup
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The earlier-source inputs for the odd branch

`ExchangedFactorSetup` records the literal conclusions and notation of
14.6.12, including the preimages in H and the moved spaces in U/Z.
It is an input interface, not a proof of 14.6.12. Its construction remains
with the singleton and quintic-recognition source owners. The residual
order is the elementary p² conclusion of the preceding primitive setup.

`MaximalOddPrime` retains the further choice made immediately before
14.6.14, over every actual outside subgroup. It must not be replaced by
maximality among the primes occurring in one chosen H.

Source: Aschbacher--Smith, printed pp.1030--1032, 14.6.12 and the paragraph
preceding 14.6.14. No fitting, local-normalizer, or suitable-vector conclusion
is included in these inputs.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G]

/-- The maximal-prime choice on printed p.1032, using H'/O₂(H') throughout. -/
def MaximalOddPrime (T M : Subgroup G) (p : ℕ) : Prop :=
  ∀ H' ∈ Chapter1.HOutside G (T : Set G) (M : Set G),
    ∀ q : ℕ, q.Prime → Odd q → pCore q (H' ⧸ pCore 2 H') ≠ ⊥ → q ≤ p

/-- Earlier-source exchanged factors, with actual preimages and quotient action.
The normalization fields are the immediate direct-product consequences of
14.6.12(2), recorded to make the group-level consumer independent of markings. -/
structure ExchangedFactorSetup {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (T : Subgroup G) (p : ℕ)
    (H0 H1 H2 : Subgroup G) : Prop where
  prime : p = 3 ∨ p = 5
  residual_card : Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = p ^ 2
  zero_le : H0 ≤ H
  first_le : H1 ≤ H0
  second_le : H2 ≤ H0
  join_eq : H1 ⊔ H2 = H0
  index : H0.relIndex H = 2
  core_le_first : H.pCoreIn 2 ≤ H1
  core_le_second : H.pCoreIn 2 ≤ H2
  actors_disjoint : Disjoint (actorImage H H1) (actorImage H H2)
  actors_commute : ∀ x ∈ actorImage H H1, ∀ y ∈ actorImage H H2, Commute x y
  first_model : Nonempty (actorImage H H1 ≃* DihedralGroup p)
  second_model : Nonempty (actorImage H H2 ≃* DihedralGroup p)
  normalizes_first : H0 ≤ normalizer (H1 : Set G)
  normalizes_second : H0 ≤ normalizer (H2 : Set G)
  exchanged : ∃ x ∈ T, x ∉ normalizer (H1 : Set G) ∧
    H1.map (MulAut.conj x⁻¹).toMonoidHom = H2
  split : subspaceCommutator a.representation ⊤ (actorImage H H1) ⊔
    subspaceCommutator a.representation ⊤ (actorImage H H2) =
      subspaceCommutator a.representation ⊤ ⊤
  disjoint : Disjoint (subspaceCommutator a.representation ⊤ (actorImage H H1))
    (subspaceCommutator a.representation ⊤ (actorImage H H2))
  first_dimension :
    (p = 3 ∧ (Module.finrank (ZMod 2)
      (subspaceCommutator a.representation ⊤ (actorImage H H1)) = 2 ∨
      Module.finrank (ZMod 2)
      (subspaceCommutator a.representation ⊤ (actorImage H H1)) = 4)) ∨
    (p = 5 ∧ Module.finrank (ZMod 2)
      (subspaceCommutator a.representation ⊤ (actorImage H H1)) = 4)
  second_dimension :
    (p = 3 ∧ (Module.finrank (ZMod 2)
      (subspaceCommutator a.representation ⊤ (actorImage H H2)) = 2 ∨
      Module.finrank (ZMod 2)
      (subspaceCommutator a.representation ⊤ (actorImage H H2)) = 4)) ∨
    (p = 5 ∧ Module.finrank (ZMod 2)
      (subspaceCommutator a.representation ⊤ (actorImage H H2)) = 4)
  point_first : Z ≤ ⁅U,residual H1⁆
  point_second : Z ≤ ⁅U,residual H2⁆

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
