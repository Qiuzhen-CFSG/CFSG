module

public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.NontrivialTwoCore.CoreLift
public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.NontrivialTwoCore.CoreOrder
public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.NontrivialTwoCore.Representation

/-!
# The nontrivial projective two-core branch: order reduction

The full symplectic preimage has nonsolvable ambient group and maps its
two-core onto the projective two-core. Once representation theory proves
extraspeciality, elementary rank at most two, and relative self-centralization,
the order is forced to be thirty-two by the intrinsic Frattini-action argument.
This supplies all four clauses of `HasExtraspecialLiftCore` from those three
structural inputs.

The theorem below is conditional. Establishing its structural inputs from
maximality, irreducibility, nonsolvability, and a nontrivial projective two-core
remains necessary for the unconditional maximal-subgroup theorem.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSp4Three

/-- In a nonsolvable projective subgroup the order clause follows from
extraspeciality, elementary rank at most two, and relative self-centralization.
These structural hypotheses must still be established for the maximal subgroup. -/
public theorem hasExtraspecialLiftCore_of_extraspecial_rank_two
    {M : Subgroup (PSp 2 (ZMod 3))} (hnsolv : ¬ Group.IsSolvable M)
    (hspecial : IsExtraspecial 2 (pCore 2 (fullPreimage M)))
    (hrank : ∀ E : Subgroup (pCore 2 (fullPreimage M)),
      IsElementaryAbelian 2 E → Nat.card E < 8)
    (hcentral : Subgroup.centralizer
      (pCore 2 (fullPreimage M) : Set (fullPreimage M)) ≤ pCore 2 (fullPreimage M)) :
    HasExtraspecialLiftCore M := by
  let := hspecial
  exact ⟨hspecial, NontrivialTwoCore.card_eq_thirty_two_of_extraspecial_rank_two
    (fullPreimage_not_isSolvable M hnsolv) hrank hcentral, hrank, hcentral⟩

end Matrix.PSp4Three
