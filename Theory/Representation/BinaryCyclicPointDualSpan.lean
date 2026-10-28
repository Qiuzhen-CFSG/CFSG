module

public import Theory.Representation.BinaryTransvectionGroups.Duality

/-!
# A cyclic point detects every invariant dual subspace

If the orbit of an original point spans the entire module, a subspace
of the dual stable under the original contragredient actor cannot
annihilate that point unless it is zero. This retains the whole module
and needs no decomposition or invariant complement.

Source application: Aschbacher--Smith12.7.18, printed p.845.
-/

public section
open Subgroup BinaryLinear BinaryTransvectionGroups
namespace Representation
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A cyclic point has a nonzero restriction to every nonzero stable dual
subspace, without any semisimplicity hypothesis. -/
theorem dual_subspace_eq_bot_of_cyclic_point_annihilation
    (H : Subgroup (BinaryLinear.GL V)) (x : V)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun g : H => g.val x)) = ⊤)
    (B : Submodule (ZMod 2) (DualSpace V))
    (hB : dualGroup H ≤ parabolic B)
    (hx : ∀ f ∈ B, f x = 0) : B = ⊥ := by
  apply bot_unique
  intro f hf
  apply LinearMap.ext
  intro v
  have horbit : Submodule.span (ZMod 2) (Set.range (fun g : H => g.val x)) ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,rfl⟩
    have hm : contragredient g.val⁻¹ f ∈ B :=
      (hB ⟨g.val⁻¹,H.inv_mem g.property,rfl⟩ f).mpr hf
    have he := hx _ hm
    exact he
  rw [hspan] at horbit
  exact horbit (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) V))

end Representation
