module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.NormNum

/-!
# The section of the noncentral involution centralizer used for its order

Held Section 4.2 constructs a normal subgroup A isomorphic to A6 in the
actual centralizer C_G(mu), with quotient dihedral of order eight. This
interface records that genuine subgroup and both multiplicative equivalences.
`DihedralGroup 4` has four rotations and total order eight. Normality is
relative to C_G(mu), not to G. No splitting is assumed here.

The cardinality lemma is conditional: Lagrange's formula gives 8 * 360 = 2880.
The source's construction of this section is a separate proof obligation.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), DOI 10.1215/ijm/1256053756,
Lemma 4.2, especially printed pp.234--235.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis
universe u

/-- A normal A6 subgroup with actual dihedral quotient of order eight. -/
public structure AlternatingSixSection (C : Type u) [Group C] where
  subgroup : Subgroup C
  normal : subgroup.Normal
  alternatingEquiv : subgroup ≃* alternatingGroup (Fin 6)
  quotientEquiv : letI := normal; (C ⧸ subgroup) ≃* DihedralGroup 4

public theorem AlternatingSixSection.card {C : Type u} [Group C]
    (s : AlternatingSixSection C) : Nat.card C = 2880 := by
  let := s.normal
  rw [card_eq_card_quotient_mul_card_subgroup s.subgroup,
    Nat.card_congr s.alternatingEquiv.toEquiv,
    Nat.card_congr s.quotientEquiv.toEquiv,
    DihedralGroup.nat_card, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis
