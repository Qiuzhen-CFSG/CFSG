module

public import Theory.GroupTheory.FaithfulNormalRestriction
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.Quotient

/-!
# The faithful action of a constituent stabilizer

A constituent for a normal subgroup is invariant under that subgroup. Its
setwise stabilizer therefore contains the normal subgroup, and its literal
stabilizer representation restricts to the original constituent action.
When this action is faithful and the ambient normal-subgroup centralizer is
trivial, the whole stabilizer action is faithful. Irreducibility also passes
to the copy of the normal subgroup inside the stabilizer.

This supplies the kernel and actor-transport steps in the constituent
selection arguments of Aschbacher–Smith, *The Classification of Quasithin
Groups*, A.1.42 and D.3.9, retaining the original subspace and operators.
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (N : Subgroup G)
  (J : Subrepresentation (ρ.comp N.subtype))

/-- A constituent's original actor lies in its setwise stabilizer. -/
theorem le_constituent_stabilizer : N ≤ subspaceStabilizer ρ J.toSubmodule := by
  exact le_subspaceStabilizer ρ J.toSubmodule
    (fun n hn v hv => J.apply_mem_toSubmodule ⟨n, hn⟩ hv)

/-- The literal stabilizer action is faithful if the normal constituent is
faithful and its normal actor has trivial ambient centralizer. -/
theorem stabilizerRepresentation_injective_of_faithful_normal_constituent
    [N.Normal] (hf : Function.Injective J.toRepresentation)
    (hc : centralizer (N : Set G) = ⊥) :
    Function.Injective (stabilizerRepresentation ρ J.toSubmodule) := by
  apply MonoidHom.injective_of_injective_normal_inclusion N _
    (le_constituent_stabilizer ρ N J) _ _ hc
  exact hf

/-- The restriction to the literal subgroup inside the stabilizer retains
the irreducibility of the selected constituent. -/
theorem stabilizerRepresentation_constituent_restriction_irreducible
    (hirr : J.toRepresentation.IsIrreducible) :
    Representation.IsIrreducible ((stabilizerRepresentation ρ J.toSubmodule).comp
      (N.subgroupOf (subspaceStabilizer ρ J.toSubmodule)).subtype) := by
  let e := subgroupOfEquivOfLe (le_constituent_stabilizer ρ N J)
  exact (irreducible_comp_surjective_iff e.toMonoidHom e.surjective
    J.toRepresentation).mpr hirr

end Representation.BinaryOffender
