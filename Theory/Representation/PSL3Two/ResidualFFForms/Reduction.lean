module

public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# From residual-invariant forms to invariant forms

The fixed space of a normal subgroup is a representation of the quotient.
In characteristic two, a nonzero module for a finite two-group has a nonzero
fixed vector. Thus vanishing of the whole group's invariants implies vanishing
of the invariants of any normal subgroup with two-group quotient.

Apply this to the action on bilinear forms, realized as `linHom ρ ρ.dual`.
It suffices to exclude forms invariant under the whole group to exclude forms
invariant under its two-residual. No semisimplicity or nondegeneracy is used.

This is a restriction step for the constituent argument in
Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two* (1993),
(3.8), printed p.878, using the modular fixed-vector theorem.
-/

public section

set_option backward.isDefEq.respectTransparency false
open Representation Subgroup

namespace BinaryLinearThree.ResidualFFForms

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Vanishing of invariants persists on a normal subgroup with two-group quotient. -/
theorem invariants_restrict_eq_bot
    (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal]
    (hN : IsPGroup 2 (G ⧸ N)) (hρ : ρ.invariants = ⊥) :
    Representation.invariants (ρ.comp N.subtype) = ⊥ := by
  classical
  by_contra hn
  let U := fixedSubrepresentationOfNormal ρ N
  let : Nontrivial U.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hn
  have hk : N ≤ U.toRepresentation.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro v
    exact Subtype.ext (v.property ⟨n, hn⟩)
  let σ := quotientOfLEKer U.toRepresentation N hk
  have hc : ringChar (ZMod 2) = 2 := ringChar.eq (ZMod 2) 2
  obtain ⟨v, hv, hfix⟩ := pGroup_fix_nonzero_vector
    (by rw [hc]; decide) (hc.symm ▸ hN) σ
  have hvG : (v : V) ∈ ρ.invariants := by
    intro g
    exact congrArg Subtype.val (hfix (QuotientGroup.mk' N g))
  rw [hρ, Submodule.mem_bot] at hvG
  exact hv (Subtype.ext hvG)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Fixedness for the Hom action is simultaneous invariance of the bilinear form. -/
theorem mem_form_invariants_iff (ρ : Representation (ZMod 2) G V)
    (N : Subgroup G) (B : LinearMap.BilinForm (ZMod 2) V) :
    B ∈ Representation.invariants ((ρ.linHom ρ.dual).comp N.subtype) ↔
      ∀ g ∈ N, ∀ v w, B (ρ g v) (ρ g w) = B v w := by
  constructor
  · intro h g hg v w
    have he := LinearMap.congr_fun (LinearMap.congr_fun (h ⟨g⁻¹, N.inv_mem hg⟩) v) w
    simpa only [MonoidHom.comp_apply, linHom_apply, dual_apply,
      LinearMap.comp_apply, Module.Dual.transpose_apply, Subgroup.subtype_apply, inv_inv] using he
  · intro h g
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    exact h g.val⁻¹ (N.inv_mem g.property) v w

/-- Excluding whole-group invariant forms suffices for two-residual invariant forms. -/
theorem form_zero_of_residual_invariance
    (ρ : Representation (ZMod 2) G V)
    (hzero : ∀ B : LinearMap.BilinForm (ZMod 2) V,
      (∀ g v w, B (ρ g v) (ρ g w) = B v w) → B = 0)
    (B : LinearMap.BilinForm (ZMod 2) V)
    (hB : ∀ g ∈ pResidual 2 G, ∀ v w, B (ρ g v) (ρ g w) = B v w) : B = 0 := by
  let τ : Representation (ZMod 2) G (LinearMap.BilinForm (ZMod 2) V) := ρ.linHom ρ.dual
  have hbot : Representation.invariants (k := ZMod 2)
      (G := G) (V := LinearMap.BilinForm (ZMod 2) V) τ = ⊥ := by
    apply le_bot_iff.mp
    intro C hC
    apply hzero C
    intro g v w
    exact (mem_form_invariants_iff ρ ⊤ C).mp (fun g => hC g.val)
      g (Subgroup.mem_top g) v w
  have hres := invariants_restrict_eq_bot (V := LinearMap.BilinForm (ZMod 2) V) τ (pResidual 2 G)
    (isPGroup_quotient_pResidual 2) hbot
  have hmem := (mem_form_invariants_iff ρ (pResidual 2 G) B).mpr hB
  rwa [hres, Submodule.mem_bot] at hmem

end BinaryLinearThree.ResidualFFForms
