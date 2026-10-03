module

public import Theory.SpecificGroups.ReeTwo.Sylow
public import Theory.SpecificGroups.ReeTwo.CoreFaithfulness

/-!
# The center of the Ree two Sylow model

Commutation with root 3 forces the cyclic-four coordinate of a central
Sylow element to vanish: its action on the first three nonconstant core
coordinates is faithful. The remaining element lies in the core center,
which consists of the identity and root 12.

Only the four possible cyclic coordinates are checked by kernel reduction;
the core calculation uses the proved polynomial coordinate identities.
Source: Shinoda (1975), (2.3) and (3.1), pp. 81–83.
-/

namespace ReeTwo.SylowModel
private theorem coordinate_action_check : ∀ t : FiveFour.Cyclic 4,
    (Core.complementAction (SemidirectProduct.inr t) (Core.root 0)).b1 = (Core.root 0).b1 →
    (Core.complementAction (SemidirectProduct.inr t) (Core.root 0)).b2 = (Core.root 0).b2 →
    (Core.complementAction (SemidirectProduct.inr t) (Core.root 0)).b3 = (Core.root 0).b3 →
    t = 1 := by decide +kernel

/-- Every nonidentity central element of the Sylow model is root 12. -/
public theorem eq_one_or_root_twelve_of_mem_center (g : SylowModel) (hg : g ∈ Subgroup.center SylowModel) :
    g = 1 ∨ g = root 9 := by
  have hc : g.left * Core.complementAction (SemidirectProduct.inr g.right) (Core.root 0) =
      Core.root 0 * g.left := by
    have h := congrArg SemidirectProduct.left (Subgroup.mem_center_iff.mp hg (root 0)).symm
    change g.left * Core.complementAction (SemidirectProduct.inr g.right) (Core.root 0) =
      Core.root 0 * Core.complementAction (SemidirectProduct.inr 1) g.left at h
    simpa only [map_one, MulAut.one_apply] using h
  have ht : g.right = 1 := by
    apply coordinate_action_check
    · exact add_left_cancel (by
        simpa only [show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl,
          Core.mul, add_comm (Core.root 0).b1] using congrArg Core.b1 hc)
    · exact add_left_cancel (by
        simpa only [show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl,
          Core.mul, add_comm (Core.root 0).b2] using congrArg Core.b2 hc)
    · exact add_left_cancel (by
        simpa only [show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl,
          Core.mul, add_comm (Core.root 0).b3] using congrArg Core.b3 hc)
  have heq : g = SemidirectProduct.inl g.left := SemidirectProduct.ext rfl ht
  have hcore (i : CoreRoot) : g.left * Core.root i = Core.root i * g.left := by
    apply SemidirectProduct.inl_injective (φ := Core.complementAction.comp SemidirectProduct.inr)
    rw [map_mul, map_mul]
    change SemidirectProduct.inl g.left * root i = root i * SemidirectProduct.inl g.left
    rw [← heq]
    exact (Subgroup.mem_center_iff.mp hg (root i)).symm
  rcases Core.eq_one_or_last_root_of_central g.left hcore with hone | hroot
  · left
    rw [heq, hone, map_one]
  · right
    rw [heq, hroot]
    rfl
end ReeTwo.SylowModel
