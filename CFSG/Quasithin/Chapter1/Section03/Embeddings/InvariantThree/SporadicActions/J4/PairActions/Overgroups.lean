module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.Contracts

/-!
# The family of symmetric-linear overgroups of a J₄ pair

An element of `PairOvergroups S R` is an actual subgroup of the binary J₄
model containing both S and R, together with a multiplicative equivalence
to the specified ATLAS max4 subgroup. Automorphisms preserving the pair
act on this family, since isomorphism type is preserved under transport.

The existence and parity contracts below are unproved model inputs. Their
combination, through the fixed-point argument in `J4.PairActions`, supplies
compatible actions for every two-subgroup of the pair automizer. Separating
nonemptiness from parity allows the two model calculations to proceed
independently. Uniqueness is sufficient for parity, but is not required.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), citing Aschbacher's *Overgroups of Sylow
subgroups in sporadic groups* (1986). The odd-family route is a sufficient
reduction of that application, not an assertion of a source incidence count.
-/

@[expose] public section

open Subgroup
open Janko4.LocalStructure.SymmetricLinear
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- Actual overgroups of the pair with the prescribed local isomorphism type. -/
abbrev PairOvergroups (S R : Subgroup Janko4.Model) :=
  {M : Subgroup Janko4.Model // S ≤ M ∧ R ≤ M ∧ Nonempty (M ≃* max4Subgroup)}

/-- The arbitrary-pair coverage input; existence of the fixed max4 subgroup
alone does not establish this statement. -/
def MaximalFourPairCoverage : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model) (R : Subgroup Janko4.Model), PairInput S R →
      Nonempty (PairOvergroups (S : Subgroup Janko4.Model) R)

/-- The incidence input needed by the two-group fixed-point argument.
Coverage is supplied separately; the count ranges over all actual subgroups
with the displayed isomorphism type, not just a proposed list of conjugates. -/
def MaximalFourPairParity : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model) (R : Subgroup Janko4.Model), PairInput S R →
      Nonempty (PairOvergroups (S : Subgroup Janko4.Model) R) →
        ¬ 2 ∣ Nat.card (PairOvergroups (S : Subgroup Janko4.Model) R)

/-- Conjugate containment supplies an actual overgroup equivalence. -/
theorem pairOvergroups_nonempty_of_conjugate (S R : Subgroup Janko4.Model)
    (g : Janko4.Model)
    (hS : S ≤ max4Subgroup.map (MulAut.conj g).toMonoidHom)
    (hR : R ≤ max4Subgroup.map (MulAut.conj g).toMonoidHom) :
    Nonempty (PairOvergroups S R) :=
  ⟨⟨_, hS, hR, ⟨((MulAut.conj g).subgroupMap max4Subgroup).symm⟩⟩⟩

/-- Uniqueness of an existing local overgroup is one sufficient incidence bound. -/
theorem pairOvergroups_odd_of_unique (S R : Subgroup Janko4.Model)
    (hne : Nonempty (PairOvergroups S R))
    (hunique : ∀ M N : PairOvergroups S R, M.val = N.val) :
    ¬ 2 ∣ Nat.card (PairOvergroups S R) := by
  have hc : Nat.card (PairOvergroups S R) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨⟨fun M N => Subtype.ext (hunique M N)⟩, hne⟩
  rw [hc]
  decide

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
