module
public import Theory.Representation.BinaryAlternatingSixModels.TensorIrreducibility.Coordinates
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.OrbitQuotient
/-!
# Irreducibility of the actual binary A₆ tensor

Every nonzero invariant subspace has a nonzero vector fixed by the literal
Sylow two-subgroup. Its coordinates satisfy the two checked fixed equations,
so it is one of three explicit nonzero vectors. Each is cyclic by the checked
orbit certificates. Thus the original tensor of the two marked natural
four-spaces is irreducible over F₂.

Source: Aschbacher–Smith G.5.1(1,3), printed pp.342–343. This proves binary
irreducibility; it does not assert absolute irreducibility over F₄.
-/
public section
namespace BinaryAlternatingSix
open Theory.SpecificGroups.SymmetricSix Representation
open TensorIrreducibility.Native TensorIrreducibility.Certificate

theorem alternatingTensor_irreducible : IsIrreducible alternatingTensor := by
  classical
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun U => ?_⟩
  by_cases hu : U = ⊥
  · exact Or.inl hu
  right
  have hu' : U.toSubmodule ≠ ⊥ := fun he => hu (Subrepresentation.toSubmodule_injective he)
  let : Nontrivial U.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hu'
  obtain ⟨v,hv,hfix⟩ := BinaryLinearThree.IrreducibleCatalogue.binary_pGroup_fixed_vector (V := U.toSubmodule)
    (U.toRepresentation.comp a6Borel.subtype)
    (IsPGroup.of_card (show Nat.card a6Borel = 2 ^ 3 from a6Borel_order))
  have hr : R.mulVec (coords (v : TensorModule)) = coords (v : TensorModule) := by
    change (matrix 0).mulVec (coords (v : TensorModule)) = _
    rw [← matrix_action 0]
    exact congrArg coords (congrArg Subtype.val (hfix ⟨r,r_mem⟩))
  have hs : S.mulVec (coords (v : TensorModule)) = coords (v : TensorModule) := by
    change (matrix 1).mulVec (coords (v : TensorModule)) = _
    rw [← matrix_action 1]
    exact congrArg coords (congrArg Subtype.val (hfix ⟨s,s_mem⟩))
  obtain hz | ⟨a,ha⟩ := fixed_cases (coords (v : TensorModule)) hr hs
  · exact (hv (Subtype.ext (coords.map_eq_zero_iff.mp hz))).elim
  let W := U.toSubmodule.map coords.toLinearMap
  have hw : W = ⊤ := cyclic_eq_top W
    (by
      rintro x ⟨y,hy,rfl⟩
      change (matrix 2).mulVec (coords y) ∈ W
      rw [← matrix_action 2]
      exact ⟨_,U.apply_mem_toSubmodule g hy,rfl⟩)
    (by
      rintro x ⟨y,hy,rfl⟩
      change (matrix 3).mulVec (coords y) ∈ W
      rw [← matrix_action 3]
      exact ⟨_,U.apply_mem_toSubmodule h hy,rfl⟩)
    a (ha ▸ U.toSubmodule.mem_map_of_mem v.property)
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro x _
  have hx : coords x ∈ W := hw ▸ Submodule.mem_top
  obtain ⟨y,hy,he⟩ := hx
  exact coords.injective he ▸ hy
end BinaryAlternatingSix
