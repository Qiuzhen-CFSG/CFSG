module

public import Theory.AlgebraicGroup.Foundations
public import Theory.AlgebraicGroup.Variety.MorphicAction

/-!
# Morphic actions on complete varieties

This module is the orbit-geometry assembly layer used in Borovoi, *Linear Algebraic Groups*
(`Bor1`), Section 10.4.  It re-exports the `MorphicAction` boundary connecting the rational-point
group of a presented affine algebraic group to a genuine scheme morphism `G x X -> X`.  The target
`X` is a possibly non-affine reduced separated finite-type scheme from `Variety.Geometric`; its
completeness is the genuine universally-closed predicate from `Variety.Complete`.

The fixed-point endpoint in Bor1 10.4 uses the closed-orbit lemma 1.8.  One chooses a smooth
closed orbit, identifies it bijectively with the quotient by its closed stabilizer, transfers
completeness to that connected affine quotient, and applies constancy of morphisms from connected
complete varieties to affine varieties.  Closed fixed loci of normal subgroups are the induction
interface: they are complete as closed subvarieties and stable under the ambient action.  Those
claims are geometric theorems, not fields of `MorphicAction`; keeping them out of the structure
prevents the representation from silently assuming the desired fixed-point result.  The action
representation itself lives in the lower `Variety.MorphicAction` module so the reusable Bor1 1.8
closed-orbit theorem can be imported here without a module cycle.
-/
