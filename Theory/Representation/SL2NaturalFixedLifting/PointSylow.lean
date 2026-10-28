module
public import Theory.Representation.SL2NaturalFixedLifting
public import Theory.SpecificGroups.SL2.LineRootGeometry

/-!
# Sylow fixed points in central natural SL₂ covers

Every natural vector is fixed by the root subgroup on its field line.
Central fixed-kernel lifting makes the same Sylow subgroup fix every vector
above it. Sylow conjugacy then fixes any chosen cover vector by a conjugate
of any specified two-subgroup. No splitting or triviality of the covering
kernel is assumed. Source: Aschbacher–Smith 10.2.9, printed pp.750–751,
using the natural fixed-lifting assertion of I.2.3.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Representation.SL2NaturalFixedLifting
variable {F W : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Each vector of a central natural cover is fixed by a Sylow two-subgroup. -/
theorem exists_sylow_fixed_of_fixed_kernel
    (σ : Representation (ZMod 2) SL(2,F) W)
    (q : W →+ (Fin 2 → F)) (hq : Function.Surjective q)
    (he : ∀ g w, q (σ g w) = g • q w)
    (hk : ∀ w, q w = 0 → ∀ g, σ g w = w)
    (w : W) : ∃ S : Sylow 2 SL(2,F), ∀ g ∈ (S : Subgroup SL(2,F)), σ g w = w := by
  by_cases hz : q w = 0
  · exact ⟨SpecialLinearGroup.upperUnipotentSylow F 2,fun g _ => hk w hz g⟩
  let P : Submodule F (Fin 2 → F) := Submodule.span F {q w}
  have hP : Module.finrank F P = 1 := finrank_span_singleton hz
  obtain ⟨S,hS⟩ := SpecialLinearGroup.exists_sylow_fixing_line P hP
  refine ⟨S,fun g hg => fixed_lift_of_fixed_kernel σ q hq he hk g w ?_⟩
  rw [he]
  exact ((mem_fixingSubgroup_iff SL(2,F)).mp (hS ▸ hg)) (q w) (Submodule.subset_span (by simp))

/-- A conjugate of any given two-subgroup fixes the specified cover vector. -/
theorem exists_conjugate_fixed_of_fixed_kernel
    (σ : Representation (ZMod 2) SL(2,F) W)
    (q : W →+ (Fin 2 → F)) (hq : Function.Surjective q)
    (he : ∀ g w, q (σ g w) = g • q w)
    (hk : ∀ w, q w = 0 → ∀ g, σ g w = w)
    (P : Subgroup SL(2,F)) (hP : IsPGroup 2 P) (w : W) :
    ∃ g : SL(2,F), ∀ p ∈ P, σ ((MulAut.conj g) p) w = w := by
  obtain ⟨S,hS⟩ := exists_sylow_fixed_of_fixed_kernel σ q hq he hk w
  obtain ⟨Q,hQ⟩ := hP.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,F) Q S
  have hm : (Q : Subgroup SL(2,F)).map (MulAut.conj g).toMonoidHom = S := by
    have hh := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul] at hh
    exact hh
  exact ⟨g,fun p hp => hS _ (hm ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom (hQ hp))⟩
end Representation.SL2NaturalFixedLifting
