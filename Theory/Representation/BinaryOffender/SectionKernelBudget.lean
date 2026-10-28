module
public import Theory.Representation.BinaryOffender.RatioInheritance
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# Fixed-codimension budget for an embedded invariant module

An injective intertwiner realizes a smaller representation inside the original
one. Its pointwise kernel on the smaller module and its image there consume
additive parts of the full fixed-codimension budget. This is the literal kernel
form of D.2.2, using the existing invariant-subspace dimension inequality.
The Chapter 10 determinant-tensor argument uses it to retain full-actor
faithfulness while passing to a seed image.
Source: Aschbacher--Smith D.2.2, printed p.178, refs/quasithin.pdf.
-/

public noncomputable section
namespace Representation.BinaryOffender
open Subgroup
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The kernel on an invariant embedded module and its action on that module
contribute additively to the full fixed-codimension budget. -/
theorem fixedCodim_kernel_add_of_injective_intertwiner
    (ρ : Representation (ZMod 2) G V) (τ : Representation (ZMod 2) G W)
    (i : τ.IntertwiningMap ρ) (hi : Function.Injective i.toLinearMap) :
    fixedCodim ρ τ.ker + fixedCodim τ ⊤ ≤ fixedCodim ρ ⊤ := by
  let U := i.range
  have hstab : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ U.toSubmodule := by
    apply le_subspaceStabilizer
    intro a _ v hv
    exact U.apply_mem_toSubmodule a hv
  have hk : subspaceKernel ρ U.toSubmodule ⊤ = τ.ker := by
    ext a
    constructor
    · rintro ⟨_,ha⟩
      apply LinearMap.ext
      intro w
      apply hi
      have he := ha (i w) ⟨w,rfl⟩
      exact (LinearMap.congr_fun (i.isIntertwining' a) w).trans he
    · intro ha
      refine ⟨mem_top _,?_⟩
      rintro v ⟨w,rfl⟩
      have he := LinearMap.congr_fun (i.isIntertwining' a) w
      have hh : τ a w = w := LinearMap.congr_fun ha w
      change i (τ a w) = ρ a (i w) at he
      rw [hh] at he
      exact he.symm
  let E := LinearEquiv.ofInjective i.toLinearMap hi
  have he := fixedCodim_map_equivariant τ U.toRepresentation (MonoidHom.id G) E
    (fun a w => Subtype.ext (LinearMap.congr_fun (i.isIntertwining' a) w)) ⊤
  rw [Subgroup.map_id] at he
  have hdim := fixedCodim_add_finrank U.toRepresentation (⊤ : Subgroup G)
  have hfixed := (subrepresentationFixedEquiv ρ U (⊤ : Subgroup G)).finrank_eq
  have hcod : fixedCodim (subspaceImageRepresentation ρ U.toSubmodule)
      (restrictedSubgroup ρ U.toSubmodule ⊤) = fixedCodim τ ⊤ := by
    rw [fixedCodim_restrictedSubgroup ρ U.toSubmodule ⊤ hstab,he]
    omega
  have hb := fixedCodim_kernel_add_restricted_le ρ U.toSubmodule ⊤ hstab
  rwa [hk,hcod] at hb
end Representation.BinaryOffender
