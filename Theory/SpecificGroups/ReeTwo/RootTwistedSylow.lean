module

public import Theory.SpecificGroups.ReeTwo.CoreRootTwist
public import Theory.GroupTheory.SpecificGroups.FiveFour
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Nilpotent

/-!
# The alternative cyclic-four extension of the Ree core

This is the explicit split extension in which the cyclic-four generator
inverts the middle root. Its action has the same square and Frobenius
relation as the standard action. It is a comparison model, not an
identification of an actual terminal Sylow group.

Source: the verified core and root action from Shinoda (1975), pp.81–83;
the central twist is calculated in `CoreRootTwist`.
-/

@[expose] public section
namespace ReeTwo

/-- The cyclic-four action with reversed middle-root orientation. -/
def rootTwistedAction : FiveFour.Cyclic 4 →* MulAut Core :=
  FiveFour.cyclicHom (Core.rootTwist * Core.a) Core.rootTwist_a_four

/-- The split cyclic-four extension with the central twist. -/
abbrev RootTwistedSylow := Core ⋊[rootTwistedAction] FiveFour.Cyclic 4

namespace RootTwistedSylow

instance : Fintype RootTwistedSylow := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

/-- The core roots in the comparison extension. -/
def root (i : CoreRoot) : RootTwistedSylow := SemidirectProduct.inl (Core.root i)

/-- The distinguished four-element actor. -/
def actor : RootTwistedSylow := SemidirectProduct.inr (FiveFour.generator 4)

theorem card : Nat.card RootTwistedSylow = 4096 := by
  rw [SemidirectProduct.card, Core.card]
  change 1024 * Nat.card (ZMod 4) = 4096
  simp

/-- The explicit comparison actor reverses the root. -/
theorem actor_inverts_root_two : actor * root 2 * actor⁻¹ = (root 2)⁻¹ := by
  change SemidirectProduct.inr _ * SemidirectProduct.inl _ *
    (SemidirectProduct.inr _)⁻¹ = (SemidirectProduct.inl _)⁻¹
  rw [← map_inv, ← SemidirectProduct.inl_aut, ← map_inv]
  apply congrArg SemidirectProduct.inl
  rw [rootTwistedAction, FiveFour.cyclicHom_generator, Core.rootTwist_a_root_two]

/-- The intrinsic comparison subgroup corresponding to the first core. -/
def firstCore : Subgroup RootTwistedSylow :=
  Subgroup.centralizer (Subgroup.upperCentralSeries RootTwistedSylow 2 : Set RootTwistedSylow)

private theorem root_nine_commute (g : RootTwistedSylow) :
    root 9 * g = g * root 9 := by
  have hfix : rootTwistedAction g.right (Core.root 9) = Core.root 9 := by
    exact (by decide +kernel : ∀ j : FiveFour.Cyclic 4,
      rootTwistedAction j (Core.root 9) = Core.root 9) g.right
  apply SemidirectProduct.ext
  · change Core.root 9 * rootTwistedAction 1 g.left =
      g.left * rootTwistedAction g.right (Core.root 9)
    rw [map_one, MulAut.one_apply, hfix]
    change Core.mul (Core.root 9) g.left = Core.mul g.left (Core.root 9)
    apply Core.ext <;> simp [Core.mul, Core.root, Core.ofCoords]
    ring
  · simp [root]

/-- The distinguished involution lies in the intrinsic comparison core. -/
theorem root_nine_mem_firstCore : root 9 ∈ firstCore := by
  apply Subgroup.mem_centralizer_iff.mpr
  intro g _
  exact (root_nine_commute g).symm

/-- The central involution as an element of the comparison first core. -/
def centralInvolution : firstCore := ⟨root 9, root_nine_mem_firstCore⟩

end RootTwistedSylow
end ReeTwo
