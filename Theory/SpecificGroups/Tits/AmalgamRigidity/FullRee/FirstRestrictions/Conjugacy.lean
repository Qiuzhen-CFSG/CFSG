module

public import Theory.SpecificGroups.ReeTwo.SylowCenter
public import Theory.SpecificGroups.ReeTwo.Characters

/-!
# Two obstructions to inner automorphisms

Commuting with the first core root forces the cyclic-four coordinate to be
trivial. The core multiplication then excludes fixing that root while adding
the central involution to the third core root. Fixing every core root instead
forces an element into the center of the whole Sylow group.

These structural tests distinguish the first two extra endpoint restrictions
from inner automorphisms. The four-element cyclic-action test is the same
coordinate argument used in `ReeTwo.SylowCenter`.
Source: Shinoda (1975), (2.3), pp.81–82.
-/

public section
open ReeTwo
namespace Tits.AmalgamRigidity.FullRee.FirstRestrictions

private theorem cyclic_check : ∀ t : FiveFour.Cyclic 4,
    (Core.complementAction (SemidirectProduct.inr t) (Core.root 0)).b1 = 0 →
    (Core.complementAction (SemidirectProduct.inr t) (Core.root 0)).b2 = 0 →
    (Core.complementAction (SemidirectProduct.inr t) (Core.root 0)).b3 = 0 →
    t = 1 := by decide +kernel

theorem cyclic_eq_one_of_commutes (g : SylowModel)
    (h : g * SylowModel.root 0 = SylowModel.root 0 * g) : g.right = 1 := by
  have hh := congrArg SemidirectProduct.left h
  change g.left * Core.complementAction (SemidirectProduct.inr g.right) (Core.root 0) =
      Core.root 0 * Core.complementAction (SemidirectProduct.inr 1) g.left at hh
  simp only [map_one, MulAut.one_apply] at hh
  apply cyclic_check
  all_goals first
    | have he := congrArg Core.b1 hh
      simpa [show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl,
        Core.mul, Core.root, Core.ofCoords] using he
    | have he := congrArg Core.b2 hh
      simpa [show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl,
        Core.mul, Core.root, Core.ofCoords] using he
    | have he := congrArg Core.b3 hh
      simpa [show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl,
        Core.mul, Core.root, Core.ofCoords] using he

theorem core_of_commutes (g : SylowModel)
    (h : g * SylowModel.root 0 = SylowModel.root 0 * g) :
    g = SemidirectProduct.inl g.left :=
  SemidirectProduct.ext rfl (cyclic_eq_one_of_commutes g h)

theorem rootTwo_twist_impossible (g : SylowModel)
    (h0 : g * SylowModel.root 0 = SylowModel.root 0 * g)
    (h2 : g * SylowModel.root 2 =
      (SylowModel.root 2 * SylowModel.root 9) * g) : False := by
  have hg := core_of_commutes g h0
  rw [hg] at h0 h2
  have hc0 : g.left * Core.root 0 = Core.root 0 * g.left :=
    SemidirectProduct.inl_injective (by simpa only [SylowModel.root, map_mul] using h0)
  have hc2 : g.left * Core.root 2 = (Core.root 2 * Core.root 9) * g.left :=
    SemidirectProduct.inl_injective (by simpa only [SylowModel.root, map_mul] using h2)
  have h4 : g.left.b4 = 0 := by
    simpa [show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl,
      Core.mul, Core.root, Core.ofCoords] using congrArg Core.b7 hc0
  have h3 : g.left.b3 = 0 := by
    simpa [show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl,
      Core.mul, Core.root, Core.ofCoords, h4] using congrArg Core.b6 hc0
  have h2' : g.left.b2 = 0 := by
    simpa [show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl,
      Core.mul, Core.root, Core.ofCoords, h3] using congrArg Core.b5 hc0
  have h0' : g.left.b0 = 0 := by
    simpa [show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl,
      Core.mul, Core.root, Core.ofCoords] using (congrArg Core.b5 hc2).symm
  have h1 : g.left.b1 = 0 := by
    simpa [show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl,
      Core.mul, Core.root, Core.ofCoords] using (congrArg Core.b6 hc2).symm
  have he := congrArg Core.b9 hc2
  simp [show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl,
    Core.mul, Core.root, Core.ofCoords, h0', h1, h2', h3, h4] at he


theorem central_of_fixes_core (g : SylowModel)
    (h : ∀ i, g * SylowModel.root i = SylowModel.root i * g) :
    g ∈ Subgroup.center SylowModel := by
  have hg := core_of_commutes g (h 0)
  have hc : ∀ i, g.left * Core.root i = Core.root i * g.left := by
    intro i
    apply SemidirectProduct.inl_injective (φ := Core.complementAction.comp SemidirectProduct.inr)
    simpa only [map_mul, ← hg, SylowModel.root] using h i
  rcases Core.eq_one_or_last_root_of_central g.left hc with ho | hz
  · rw [hg, ho, map_one]
    exact Subgroup.one_mem _
  · have hg' : g = SylowModel.root 9 := hg.trans (congrArg SemidirectProduct.inl hz)
    rw [hg']
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply SylowModel.embedding_injective
    simpa only [map_mul, SylowModel.embedding_root] using
      Subgroup.mem_center_iff.mp Centralizer.root_twelve_central (SylowModel.embedding x)
end Tits.AmalgamRigidity.FullRee.FirstRestrictions
