module

public import Theory.Representation.BinaryOffender.FaithfulConstituentStabilizer
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.NormalSemisimpleSpan
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.GroupTheory.PGroup.SubgroupQuotient

/-!
# Generalized Fitting subgroups from irreducible normal restrictions

An irreducible restriction makes the ambient action irreducible. In a faithful
binary action the normal two-core consequently vanishes. If the normal actor
is quasisimple and its quotient is a two-group, it is therefore the entire
generalized Fitting subgroup.

The final theorem applies this argument to the literal stabilizer of a
faithful simple constituent, transporting both the normal actor and its
two-group quotient. This supplies the group-structure step for constituent
selection in Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.42 and B.1.11, printed pp.32 and 73.
-/

public section
open Subgroup Representation Theory.GroupTheory

namespace Representation

/-- Irreducibility of a subgroup restriction implies ambient irreducibility. -/
theorem irreducible_of_subgroup_restriction {F G V : Type*}
    [Field F] [Group G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (N : Subgroup G)
    (hi : IsIrreducible (ρ.comp N.subtype)) : IsIrreducible ρ := by
  let := hi
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial (ρ.comp N.subtype)
  rw [IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  rcases eq_bot_or_eq_top (S.compActors N.subtype) with h | h
  · left
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation (ρ.comp N.subtype) => U.toSubmodule) h)
  · right
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation (ρ.comp N.subtype) => U.toSubmodule) h)

/-- A faithful binary action irreducible on a normal quasisimple subgroup
identifies that subgroup with F* when the quotient is a two-group. -/
theorem generalizedFitting_eq_of_faithful_quasisimple_restriction
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal] [IsQuasisimple N]
    (hf : Function.Injective ρ) (hquot : IsPGroup 2 (G ⧸ N))
    (hi : IsIrreducible (ρ.comp N.subtype)) : generalizedFitting G = N := by
  let := irreducible_of_subgroup_restriction ρ N hi
  apply generalizedFitting_eq_of_quasisimple_two_quotient N hquot
  exact le_bot_iff.mp ((normal_p_subgroup_le_ker ρ
    (pCore 2 G) pCore_isPGroup).trans ((MonoidHom.ker_eq_bot_iff ρ).mpr hf).le)

end Representation

namespace Representation.BinaryOffender

/-- The original normal actor is exactly F* of the constituent stabilizer.
The two-group quotient is inherited from the original ambient quotient. -/
theorem constituent_stabilizer_generalizedFitting_eq
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal] [IsQuasisimple N]
    (J : Subrepresentation (ρ.comp N.subtype))
    (hfJ : Function.Injective J.toRepresentation)
    (hc : centralizer (N : Set G) = ⊥) (hquot : IsPGroup 2 (G ⧸ N))
    (hirr : J.toRepresentation.IsIrreducible) :
    generalizedFitting (subspaceStabilizer ρ J.toSubmodule) =
      N.subgroupOf (subspaceStabilizer ρ J.toSubmodule) := by
  let e := subgroupOfEquivOfLe (le_constituent_stabilizer ρ N J)
  let : IsQuasisimple (N.subgroupOf (subspaceStabilizer ρ J.toSubmodule)) :=
    IsQuasisimple.of_mulEquiv e.symm
  exact generalizedFitting_eq_of_faithful_quasisimple_restriction
    (stabilizerRepresentation ρ J.toSubmodule) _
    (stabilizerRepresentation_injective_of_faithful_normal_constituent ρ N J hfJ hc)
    (isPGroup_quotient_subgroupOf N _ hquot)
    (stabilizerRepresentation_constituent_restriction_irreducible ρ N J hirr)

end Representation.BinaryOffender
