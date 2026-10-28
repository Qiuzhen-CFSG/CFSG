module
public import Theory.Representation.NormalInvariants
public import Theory.Representation.SubrepresentationLattice

/-!
# Normal subgroups detected on a constituent

In a faithful irreducible representation, a nontrivial normal subgroup cannot
act trivially on a nonzero constituent of an overgroup. Otherwise a nonzero
constituent vector is fixed by that normal subgroup. Its ambient-invariant
fixed space is then the whole module, contradicting faithfulness.

This fixed-space form of Clifford theory is used on the actual component pair
in Aschbacher–Smith 15.2.27(2), printed p.1119.
-/

public section
open Subgroup
namespace Representation
variable {F G W : Type*} [Field F] [Group G] [AddCommGroup W] [Module F W]

/-- Every constituent detects each nontrivial ambient normal subgroup it can act on. -/
theorem normal_subgroup_not_le_constituent_kernel
    (ρ : Representation F G W) [IsIrreducible ρ] (hf : Function.Injective ρ)
    (I : Subgroup G) (C : Subrepresentation (ρ.comp I.subtype))
    [IsIrreducible C.toRepresentation]
    (N : Subgroup G) [N.Normal] (hNI : N ≤ I) (hN : N ≠ ⊥) :
    ¬ N.subgroupOf I ≤ C.toRepresentation.ker := by
  intro hk
  let : Nontrivial C.toSubmodule := Subrepresentation.irreducible_module_nontrivial C.toRepresentation
  obtain ⟨w,hw⟩ := exists_ne (0 : C.toSubmodule)
  have hw' : (w : W) ≠ 0 := fun hh => hw (Subtype.ext hh)
  have hm : (w : W) ∈ invariants (ρ.comp N.subtype) := by
    intro n
    let nI : I := ⟨n,hNI n.property⟩
    have hh : C.toRepresentation nI = 1 := hk n.property
    have hh' := congrArg (fun f : Module.End F C.toSubmodule => (f w : W)) hh
    exact hh'
  have hfix : invariants (ρ.comp N.subtype) ≠ ⊥ := by
    intro he
    rw [he,Submodule.mem_bot] at hm
    exact hw' hm
  have hle := le_ker_of_normal_invariants_ne_bot ρ N hfix
  rw [(MonoidHom.ker_eq_bot_iff ρ).mpr hf] at hle
  exact hN (bot_unique hle)
end Representation
