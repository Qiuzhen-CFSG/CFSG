module
public import Theory.Representation.NormalComponentConstituents
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient

/-!
# Faithful constituents of a normal simple subgroup

In a faithful irreducible representation, a nontrivial normal subgroup has
zero fixed space. A simple normal subgroup therefore acts nontrivially on
every nonzero constituent, and simplicity makes each constituent faithful.
Finite dimension supplies a simple submodule of the normal restriction.

This is the constituent selection in the Clifford reduction of
Aschbacher–Smith B.4.2–5 and D.3.6–9.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [FiniteDimensional (ZMod 2) V] in
theorem normal_simple_constituent_faithful
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (K : Subgroup G) [K.Normal] [IsSimpleGroup K]
    (J : Subrepresentation (ρ.comp K.subtype)) (hJ : J.toRepresentation.IsIrreducible) :
    Function.Injective J.toRepresentation := by
  have hK : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).mp inferInstance
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi K hK
  apply (MonoidHom.ker_eq_bot_iff J.toRepresentation).mp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal J.toRepresentation.ker inferInstance with hb | ht
  · exact hb
  · have hle : J.toSubmodule ≤ fixedSpace ρ K := by
      intro v hv k
      have hk : k ∈ J.toRepresentation.ker := by rw [ht]; trivial
      exact congrArg Subtype.val (LinearMap.congr_fun hk (⟨v,hv⟩ : J.toSubmodule))
    rw [hfix] at hle
    have hjbot : J = ⊥ := Subrepresentation.toSubmodule_injective (bot_unique hle)
    exact ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).ne_bot hjbot |>.elim

theorem exists_faithful_normal_simple_constituent
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (K : Subgroup G) [K.Normal] [IsSimpleGroup K] :
    ∃ J : Subrepresentation (ρ.comp K.subtype),
      J.toRepresentation.IsIrreducible ∧ Function.Injective J.toRepresentation := by
  let := hi
  let := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨J,hJ,_⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation (ρ.comp K.subtype))).resolve_left top_ne_bot
  have hj := (Subrepresentation.irreducible_iff_isAtom J).mpr hJ
  exact ⟨J,hj,normal_simple_constituent_faithful ρ hf hi K J hj⟩
end Representation
