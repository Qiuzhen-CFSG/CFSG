module
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Theory.Representation.BinaryOffender.EquivariantStabilizer

/-!
# Retaining the constituent, its central quotient and its marked line

An injective intertwiner preserves the exact setwise stabilizer of a
line. Restricting to a containing invariant subspace therefore preserves
its marking. Disjointness from fixed vectors makes the map of that line
into the genuine central quotient injective. MarkedConstituent retains
IsIrrPlus, hence the full commutator identity and the original induced
irreducible quotient action, without replacing the central submodule.

The constructor is conditional on a containing Irr+ member. Selecting
that member from B.5.6 remains a separate mathematical obligation.
These helpers stay at the owning campaign boundary until that assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.1.40,
p.31, and the first paragraph of the proof of 15.3.31, p.1132.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents
section Transport
variable {A V W : Type*} [Group A]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) A V) (σ : Representation (ZMod 2) A W)
  (f : V →ₗ[ZMod 2] W) (hf : Function.Injective f)
  (he : ∀ a v, f (ρ a v) = σ a (f v))

include hf he in
theorem embedding_stabilizer (E : Submodule (ZMod 2) V) :
    subspaceStabilizer σ (E.map f) = subspaceStabilizer ρ E := by
  have hm (v : V) : f v ∈ E.map f ↔ v ∈ E := by
    constructor
    · rintro ⟨w, hw, heq⟩
      exact hf heq ▸ hw
    · intro hv; exact ⟨v, hv, rfl⟩
  apply le_antisymm
  · intro a ha v
    have hh := ha (f v)
    rwa [← he, hm, hm] at hh
  · apply le_subspaceStabilizer
    rintro a ha _ ⟨v, hv, rfl⟩
    exact ⟨ρ a v, (ha v).mpr hv, he a v⟩

include hf in
theorem embedding_line_card (E : Submodule (ZMod 2) V) :
    Nat.card (E.map f) = Nat.card E :=
  (Nat.card_congr (Submodule.equivMapOfInjective f hf E).toEquiv).symm

include hf in
theorem embedding_line_nonzero {E : Submodule (ZMod 2) V} (hE : E ≠ ⊥) :
    E.map f ≠ ⊥ := by
  intro heq
  apply hE
  apply (Submodule.map_injective_of_injective hf)
  simpa using heq

end Transport

section Section
variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) A V)
  (L : Subgroup A) (E W : Submodule (ZMod 2) V)

theorem contained_line_image (hEW : E ≤ W) :
    (E.comap W.subtype).map W.subtype = E := by
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr hEW]

set_option backward.isDefEq.respectTransparency false in
theorem contained_line_stabilizer (hW : L ≤ subspaceStabilizer ρ W) (hEW : E ≤ W) :
    subspaceStabilizer (invariantSubspace ρ L W hW).toRepresentation
      (E.comap W.subtype) = (subspaceStabilizer ρ E).subgroupOf L := by
  have hh := embedding_stabilizer (invariantSubspace ρ L W hW).toRepresentation
    (ρ.comp L.subtype) W.subtype W.subtype_injective (fun _ _ => rfl)
    (E.comap W.subtype)
  rw [contained_line_image E W hEW] at hh
  exact hh.symm

theorem line_quotient_injective (hEW : E ≤ W)
    (hdis : Disjoint E (fixedSpace ρ L)) :
    Function.Injective (((fixedSpace ρ L).comap W.subtype).mkQ.comp
      (Submodule.inclusion hEW)) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro v hv
  have hvfix : Submodule.inclusion hEW v ∈ (fixedSpace ρ L).comap W.subtype :=
    (Submodule.Quotient.mk_eq_zero _).mp hv
  have hz : (v : V) = 0 := (Submodule.disjoint_def.mp hdis) v v.property hvfix
  exact Subtype.ext hz

/-- A genuine Irr+ constituent containing the specified line. The central
submodule and quotient action are the literal constructions from IsIrrPlus. -/
structure MarkedConstituent (P : Subgroup L) where
  space : Submodule (ZMod 2) V
  irrPlus : IsIrrPlus ρ L space
  contains : E ≤ space
  line_card : Nat.card (E.comap space.subtype) = 4
  line_stabilizer : subspaceStabilizer
    (invariantSubspace ρ L space irrPlus.choose).toRepresentation
    (E.comap space.subtype) = P
  quotient_injective : Function.Injective
    (((fixedSpace ρ L).comap space.subtype).mkQ.comp (Submodule.inclusion contains))

theorem markedConstituent_of_containment
    (P : Subgroup L) (hE : Nat.card E = 4)
    (hst : subspaceStabilizer (ρ.comp L.subtype) E = P)
    (hdis : Disjoint E (fixedSpace ρ L))
    (hW : IsIrrPlus ρ L W) (hEW : E ≤ W) :
    Nonempty (MarkedConstituent ρ L E P) := by
  refine ⟨⟨W, hW, hEW, ?_, ?_, line_quotient_injective ρ L E W hEW hdis⟩⟩
  · rw [← embedding_line_card W.subtype W.subtype_injective (E.comap W.subtype),
      contained_line_image E W hEW]
    exact hE
  · rw [contained_line_stabilizer ρ L E W hW.choose hEW]
    exact hst

end Section
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents
