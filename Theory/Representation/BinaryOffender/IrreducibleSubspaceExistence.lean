module
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Theory.Representation.BinaryOffender.Homogeneous.Embedding
/-!
# Irreducible sections inside an invariant subspace

A noncentral invariant subspace for a perfect binary actor contains an Irr⁺
subspace. Apply the minimal-dimension existence theorem to the restricted
representation, then transport its constituent through the literal inclusion.

Source: Aschbacher–Smith, A.1.40 and B.1.11, printed pp.31 and73.
-/

public section
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
theorem exists_isIrrPlus_le_of_not_fixed (ρ : Representation (ZMod 2) G V)
    (L : Subgroup G) [Group.IsPerfect L] (W : Submodule (ZMod 2) V)
    (hW : L ≤ subspaceStabilizer ρ W) (hn : ¬ W ≤ fixedSpace ρ L) :
    ∃ I, I ≤ W ∧ IsIrrPlus ρ L I := by
  let σ := (invariantSubspace ρ L W hW).toRepresentation
  let : Group.IsPerfect (⊤ : Subgroup L) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L).symm.toMonoidHom)
      Subgroup.topEquiv.symm.surjective
  have hn' : ¬ (⊤ : Submodule (ZMod 2) W) ≤ fixedSpace σ ⊤ := by
    intro hf
    apply hn
    intro v hv l
    exact congrArg Subtype.val (hf (show (⟨v,hv⟩ : W) ∈ ⊤ from by trivial) ⟨l,by trivial⟩)
  obtain ⟨I,hI⟩ := exists_isIrrPlus_of_not_fixed σ ⊤ hn'
  refine ⟨I.map W.subtype,Submodule.map_subtype_le _ _,?_⟩
  have h := hI.map_equivariant_embedding σ ρ L.subtype W.subtype
    (fun _ _ => rfl) W.subtype_injective
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h
end Representation.BinaryOffender
