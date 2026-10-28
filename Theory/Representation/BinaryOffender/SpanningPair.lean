module
public import Theory.Representation.BinaryOffender.RatioInheritance
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.ElementaryAbelian.Injective
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Sharp offender bounds on spanning subspaces

If two invariant subspaces span a faithful binary representation and neither
faithful action image has strong offenders, the full action has none either.
Restriction to the first subspace splits actor rank into kernel and image.
That kernel acts faithfully on the second subspace, so the two sharp bounds
add through the fixed-codimension restriction inequality. No disjointness of
the subspaces is needed.

This is the dimension argument for the paired central covers in
Aschbacher--Smith, 10.2.8, printed p.749, using B.7.1, pp.118--119.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- An injective change of actors and equivariant coordinates preserves the
absence of strong offenders. -/
theorem not_strong_of_equivariant {H X : Type*} [Group H] [AddCommGroup X]
    [Module (ZMod 2) X] (σ : Representation (ZMod 2) H X)
    (f : G →* H) (hf : Function.Injective f) (E : V ≃ₗ[ZMod 2] X)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    (hn : ¬ IsStrongFFModule σ) : ¬ IsStrongFFModule ρ := by
  rintro ⟨A,hA,hlt⟩
  have h := (show IsOffender ρ A from ⟨hA,hlt.le⟩).map_equivariant ρ σ f hf E hE
  apply hn
  refine ⟨A.map f,h.1,?_⟩
  rw [←fixedCodim_map_equivariant ρ σ f E hE,rank_map_injective f hf]
  exact hlt

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem rank_le_restricted_codim
    (U : Submodule (ZMod 2) V)
    (hn : ¬ IsStrongFFModule (subspaceImageRepresentation ρ U))
    (A : Subgroup G) [IsElementaryAbelian 2 A] :
    rank (restrictedSubgroup ρ U A) ≤
      fixedCodim (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) := by
  let : IsElementaryAbelian 2 (A.subgroupOf (subspaceStabilizer ρ U)) :=
    IsElementaryAbelian.comap_of_injective (subspaceStabilizer ρ U).subtype
      (subspaceStabilizer ρ U).subtype_injective A
  let : IsElementaryAbelian 2 (restrictedSubgroup ρ U A) :=
    IsElementaryAbelian.map (subspaceActionHom ρ U)
  by_cases h : restrictedSubgroup ρ U A = ⊥
  · simp [h, rank]
  · exact Nat.le_of_not_gt (fun hh => hn ⟨_, ⟨h,inferInstance⟩,hh⟩)

/-- Two invariant subspaces without strong image offenders have no strong
offender on their sum, even when the subspaces intersect. -/
theorem pair_not_strong (hf : Function.Injective ρ)
    (U W : Submodule (ZMod 2) V) (hUW : U ⊔ W = ⊤)
    (hU : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ U)
    (hW : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ W)
    (hnU : ¬ IsStrongFFModule (subspaceImageRepresentation ρ U))
    (hnW : ¬ IsStrongFFModule (subspaceImageRepresentation ρ W)) :
    ¬ IsStrongFFModule ρ := by
  rintro ⟨A,hA,hlt⟩
  let : IsElementaryAbelian 2 A := hA.2
  let B := subspaceKernel ρ U A
  have hBA : B ≤ A := subspaceKernel_le ρ U A
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective
    (inclusion hBA) (inclusion_injective hBA)
  have hBW : subspaceKernel ρ W B = ⊥ := by
    apply bot_unique
    intro b hb
    apply hf
    apply LinearMap.ext
    intro v
    have hv : v ∈ U ⊔ W := hUW ▸ Submodule.mem_top
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_one]
    change ρ b (u+w) = u+w
    rw [map_add, hb.1.2 u hu, hb.2 w hw]
  have hrB := rank_subspaceKernel_add_image ρ W B (le_top.trans hW)
    (IsElementaryAbelian.isPGroup 2 B)
  rw [hBW,rank_bot,zero_add] at hrB
  have hrA := rank_subspaceKernel_add_image ρ U A (le_top.trans hU)
    (IsElementaryAbelian.isPGroup 2 A)
  have hc := fixedCodim_kernel_add_restricted_le ρ U A (le_top.trans hU)
  have hUbound := rank_le_restricted_codim ρ U hnU A
  have hWbound := rank_le_restricted_codim ρ W hnW B
  have hWcodim : fixedCodim (subspaceImageRepresentation ρ W)
      (restrictedSubgroup ρ W B) ≤ fixedCodim ρ B := by
    have hh := fixedCodim_kernel_add_restricted_le ρ W B (le_top.trans hW)
    omega
  change fixedCodim ρ B + _ ≤ _ at hc
  change rank B + _ = _ at hrA
  omega
end Representation.BinaryOffender
