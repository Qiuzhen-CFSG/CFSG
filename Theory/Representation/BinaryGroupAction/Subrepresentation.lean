module
public import Theory.Representation.BinaryGroupAction
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# Displacement on a binary subrepresentation

The inclusion of an invariant subspace carries the moved space of its
restricted representation to the ambient displacement on that subspace.
The binary submodule/subgroup correspondence then identifies the literal
group-action commutator subgroup and preserves its cardinality. Thus its
order is two to the restricted moved-space dimension.

This transports the fixed-complement calculation in Aschbacher--Smith
D.2.25, printed p.190, without replacing either the actor or the inclusion.
-/

open Representation.BinaryOffender
namespace Representation.BinaryGroupAction
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The restricted group commutator is the original subspace displacement. -/
public theorem commutatorSubgroup_eq (U : Submodule (ZMod 2) V) (A : Subgroup G) :
    letI := action ρ
    commutatorSubgroup A (Multiplicative V) (submoduleEquivSubgroup U) =
      submoduleEquivSubgroup (subspaceCommutator ρ U A) := by
  let := action ρ
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a, v, hv, rfl⟩
    change -v.toAdd + ρ a v.toAdd ∈ subspaceCommutator ρ U A
    rw [add_comm, ← sub_eq_add_neg]
    exact Submodule.subset_span ⟨a, a.property, v.toAdd, hv, rfl⟩
  · apply (submoduleEquivSubgroup (V := V)).symm.le_iff_le.mp
    change subspaceCommutator ρ U A ≤
      (submoduleEquivSubgroup (V := V)).symm
        (commutatorSubgroup A (Multiplicative V) (submoduleEquivSubgroup U))
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, hv, rfl⟩
    change Multiplicative.ofAdd (ρ a v - v) ∈
      commutatorSubgroup A (Multiplicative V) (submoduleEquivSubgroup U)
    apply Subgroup.subset_closure
    refine ⟨⟨a, ha⟩, Multiplicative.ofAdd v, hv, ?_⟩
    change Multiplicative.ofAdd (ρ a v - v) = Multiplicative.ofAdd (-v + ρ a v)
    congr 1
    exact sub_eq_neg_add _ _

/-- The moved space of a subrepresentation maps to its ambient displacement
along the literal submodule inclusion. -/
public theorem subrepresentation_moved_map (W : Subrepresentation ρ) (A : Subgroup G) :
    (subspaceCommutator W.toRepresentation ⊤ A).map W.toSubmodule.subtype =
      subspaceCommutator ρ W.toSubmodule A := by
  have he := subspaceCommutator_map_embedding ρ W.toRepresentation
    (MonoidHom.id G) W.toSubmodule.subtype (fun _ _ => rfl) A ⊤
  simpa only [Subgroup.map_id, Submodule.map_top, Submodule.range_subtype] using he.symm

/-- Restricted linear displacement identifies the literal ambient subgroup. -/
public theorem subrepresentation_commutator_eq (W : Subrepresentation ρ) (A : Subgroup G) :
    letI := action ρ
    commutatorSubgroup A (Multiplicative V) (submoduleEquivSubgroup W.toSubmodule) =
      submoduleEquivSubgroup
        ((subspaceCommutator W.toRepresentation ⊤ A).map W.toSubmodule.subtype) := by
  let := action ρ
  rw [commutatorSubgroup_eq, subrepresentation_moved_map]

/-- The cardinality of ambient displacement on a subrepresentation is the
binary power of the displacement dimension in the restricted representation. -/
public theorem subrepresentation_commutator_card [FiniteDimensional (ZMod 2) V]
    (W : Subrepresentation ρ) (A : Subgroup G) :
    letI := action ρ
    Nat.card (commutatorSubgroup A (Multiplicative V)
      (submoduleEquivSubgroup W.toSubmodule)) =
        2 ^ Module.finrank (ZMod 2) (subspaceCommutator W.toRepresentation ⊤ A) := by
  let := action ρ
  rw [subrepresentation_commutator_eq, card_submoduleEquivSubgroup]
  have he := Submodule.equivMapOfInjective W.toSubmodule.subtype
    W.toSubmodule.subtype_injective (subspaceCommutator W.toRepresentation ⊤ A)
  rw [← Nat.card_congr he.toEquiv, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
end Representation.BinaryGroupAction
