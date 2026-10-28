module
public import Theory.Representation.BinaryGroupAction.Subrepresentation
public import Theory.Representation.SubrepresentationLattice
public import Theory.Representation.BinaryParabolicNatural.Basic
/-!
# Full movement makes a binary plane irreducible

A proper nonzero invariant subspace in dimension two leaves a binary line
quotient. Its automorphism group is trivial, so it contains every displacement,
contrary to full commutator generation. This supplies the actual irreducibility
step in Aschbacher--Smith13.5.21(iii), without a chosen orbit or model.
-/
public section
namespace Representation.BinaryOffender
open Subgroup
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) G W)

theorem irreducible_of_rank_two_full_movement
    (hd : Module.finrank (ZMod 2) W=2)
    (hm : subspaceCommutator ρ ⊤ ⊤=⊤) : IsIrreducible ρ := by
  let : Nontrivial W := Module.nontrivial_of_finrank_pos (by omega : 0<Module.finrank (ZMod 2) W)
  rw [IsIrreducible,isSimpleOrder_iff]
  refine ⟨inferInstance,fun N=>?_⟩
  by_cases hb : N=⊥
  · exact Or.inl hb
  by_cases ht : N=⊤
  · exact Or.inr ht
  exfalso
  have hNb : N.toSubmodule≠⊥ := fun h => hb (Subrepresentation.toSubmodule_injective h)
  have hNt : N.toSubmodule≠⊤ := fun h => ht (Subrepresentation.toSubmodule_injective h)
  have hpos : 0<Module.finrank (ZMod 2) N.toSubmodule :=
    Nat.pos_of_ne_zero (fun h=>hNb (Submodule.finrank_eq_zero.mp h))
  have hlt := Submodule.finrank_lt hNt
  have hsum := Submodule.finrank_quotient_add_finrank N.toSubmodule
  have hqdim : Module.finrank (ZMod 2) (W⧸N.toSubmodule)=1 := by omega
  have hf (g:G) : N.quotientRepresentation g=1 := by
    have hh := BinaryParabolicNatural.linear_one_trivial hqdim
      (LinearMap.GeneralLinearGroup.toLinearEquiv (N.quotientRepresentation.asGroupHom g))
    exact congrArg LinearEquiv.toLinearMap hh
  have hle : subspaceCommutator ρ ⊤ ⊤≤N.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have hh := LinearMap.congr_fun (hf g) (Submodule.Quotient.mk v)
    change Submodule.Quotient.mk (ρ g v)=Submodule.Quotient.mk v at hh
    change N.toSubmodule.mkQ (ρ g v-v)=0
    rw [map_sub]
    exact sub_eq_zero.mpr hh
  exact hNt (top_unique (hm ▸ hle))
end Representation.BinaryOffender
