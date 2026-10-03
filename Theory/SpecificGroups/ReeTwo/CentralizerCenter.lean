module

public import Theory.SpecificGroups.ReeTwo.Centralizer

/-!
# The distinguished involution of the Ree two centralizer

The specified complement has trivial center. A central element of the
semidirect product therefore lies in the core, whose root commutators
force it to be the identity or the last root. The two finite checks use
kernel reduction on the verified multiplication, without an external
group computation. Thus every nonidentity central element is root 12.

This verifies the q = 2 central-involution identification used with
Shinoda (1975), (3.1)–(3.2), p. 83.
-/

namespace ReeTwo.Centralizer

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem core_center_check : ∀ g : Core,
    (∀ i : CoreRoot, Core.root i * g = g * Core.root i) →
      g = 1 ∨ g = Core.root 9 := by decide +kernel

private theorem complement_center_check : ∀ g : FiveFour.Group,
    FiveFour.c * g = g * FiveFour.c →
      FiveFour.a * g = g * FiveFour.a → g = 1 := by decide +kernel

/-- The center of the concrete centralizer has just the identity and root 12. -/
public theorem eq_one_or_root_twelve_of_mem_center
    (g : Centralizer) (hg : g ∈ Subgroup.center Centralizer) :
    g = 1 ∨ g = root 9 := by
  have hright (t : Core.complement) : t * g.right = g.right * t :=
    congrArg (fun h : Centralizer => h.right)
      (Subgroup.mem_center_iff.mp hg (SemidirectProduct.inr t))
  have hrightOne : g.right = 1 := by
    apply Core.complementEquiv.symm.injective
    rw [map_one]
    apply complement_center_check
    · simpa only [map_mul, Core.complementEquiv.symm_apply_apply] using
        congrArg Core.complementEquiv.symm (hright (Core.complementEquiv FiveFour.c))
    · simpa only [map_mul, Core.complementEquiv.symm_apply_apply] using
        congrArg Core.complementEquiv.symm (hright (Core.complementEquiv FiveFour.a))
  have heq : g = SemidirectProduct.inl g.left := by
    apply SemidirectProduct.ext
    · rfl
    · exact hrightOne
  have hcore (i : CoreRoot) : Core.root i * g.left = g.left * Core.root i := by
    apply SemidirectProduct.inl_injective (φ := Core.complement.subtype)
    rw [map_mul, map_mul]
    change root i * SemidirectProduct.inl g.left = SemidirectProduct.inl g.left * root i
    rw [← heq]
    exact Subgroup.mem_center_iff.mp hg (root i)
  rcases core_center_check g.left hcore with hone | hroot
  · left
    rw [heq, hone, map_one]
  · right
    rw [heq, hroot]
    rfl

/-- The unique nonidentity central element is the distinguished involution. -/
public theorem eq_root_twelve_of_mem_center_of_ne_one
    (g : Centralizer) (hg : g ∈ Subgroup.center Centralizer) (hne : g ≠ 1) :
    g = root 9 := (eq_one_or_root_twelve_of_mem_center g hg).resolve_left hne

end ReeTwo.Centralizer
