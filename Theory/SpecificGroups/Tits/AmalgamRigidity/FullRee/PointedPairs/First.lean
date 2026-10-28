module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.Core
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.FirstRestrictions.Generators

/-!
# First-endpoint involutions outside the binary Ree Borel

Projection to the explicit group of order 20 reduces every involution outside
the Sylow subgroup to the chosen Weyl fiber. The core cocycle calculation then
reduces that fiber to the Weyl involution or its product with root 9. The
conjugating element remains in the original computable Sylow model.

Source: the marked first endpoint of Aschbacher–Smith F.4.8, using Shinoda's
ordered core and the verified `FirstRestrictions.fromS` embedding.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.PointedPairs
open ReeTwo FirstRestrictions

theorem fiveFour_involution_conjugate (x : FiveFour.Group)
    (hx : x ^ 2 = 1) (hn : x.left ≠ 1) :
    ∃ t : FiveFour.Cyclic 4, x = SemidirectProduct.inr t * FiveFour.r *
      (SemidirectProduct.inr t)⁻¹ := by
  exact (by decide +kernel : ∀ x : FiveFour.Group, x ^ 2 = 1 → x.left ≠ 1 →
    ∃ t : FiveFour.Cyclic 4, x = SemidirectProduct.inr t * FiveFour.r *
      (SemidirectProduct.inr t)⁻¹) x hx hn

theorem mem_firstB_iff (x : E) : x ∈ fromS.range ↔ x.right.left = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hx
    refine ⟨⟨x.left, x.right.right⟩, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · apply SemidirectProduct.ext
      · exact hx.symm
      · rfl

def firstRepresentative (e : ZMod 2) : E :=
  SemidirectProduct.inl (Core.root 9 ^ e.val) * SemidirectProduct.inr FiveFour.r

theorem first_fiber_conjugate (x : E) (hx : x ^ 2 = 1) (hr : x.right = FiveFour.r) :
    ∃ g : Core, ∃ e : ZMod 2,
      x = SemidirectProduct.inl g * firstRepresentative e * (SemidirectProduct.inl g)⁻¹ := by
  have hc : x.left * Core.r x.left = 1 := by
    have he := congrArg SemidirectProduct.left hx
    simpa only [pow_two, SemidirectProduct.mul_left, hr, Core.complementAction_r, SemidirectProduct.one_left] using he
  obtain ⟨g, e, he⟩ := rCocycle_conjugate x.left hc
  refine ⟨g, e, ?_⟩
  have hm : (SemidirectProduct.inr FiveFour.r : E) * SemidirectProduct.inl g⁻¹ *
      (SemidirectProduct.inr FiveFour.r)⁻¹ = SemidirectProduct.inl (Core.r g⁻¹) := by
    simpa only [Core.complementAction_r, map_inv] using
      (SemidirectProduct.inl_aut (φ := Core.complementAction) FiveFour.r g⁻¹).symm
  calc
    x = SemidirectProduct.inl x.left * SemidirectProduct.inr FiveFour.r := by
      rw [← hr, SemidirectProduct.inl_left_mul_inr_right]
    _ = SemidirectProduct.inl g * SemidirectProduct.inl (Core.root 9 ^ e.val) *
        SemidirectProduct.inl (Core.r g⁻¹) * SemidirectProduct.inr FiveFour.r := by
      rw [he, map_mul, map_mul]
    _ = _ := by rw [← hm]; unfold firstRepresentative; simp only [map_inv]; group

theorem first_involution_conjugate (x : E) (hx : x ^ 2 = 1) (hn : x ∉ fromS.range) :
    ∃ b : SylowModel, ∃ e : ZMod 2,
      x = fromS b * firstRepresentative e * (fromS b)⁻¹ := by
  have hp : x.right ^ 2 = 1 := by
    exact congrArg (SemidirectProduct.rightHom (φ := Core.complementAction)) hx
  have hn' : x.right.left ≠ 1 := fun h => hn ((mem_firstB_iff x).mpr h)
  obtain ⟨t, ht⟩ := fiveFour_involution_conjugate x.right hp hn'
  let b : SylowModel := SemidirectProduct.inr t
  let y : E := (fromS b)⁻¹ * x * fromS b
  have hy : y ^ 2 = 1 := by
    dsimp [y]
    calc
      _ = (fromS b)⁻¹ * x^2 * fromS b := by simp only [pow_two]; group
      _ = 1 := by rw [hx]; group
  have hr : y.right = FiveFour.r := by
    change (SemidirectProduct.inr t)⁻¹ * x.right * SemidirectProduct.inr t = FiveFour.r
    rw [ht]
    group
  obtain ⟨g,e,he⟩ := first_fiber_conjugate y hy hr
  refine ⟨b * SemidirectProduct.inl g, e, ?_⟩
  have hg : fromS (SemidirectProduct.inl g) = (SemidirectProduct.inl g : E) := rfl
  rw [map_mul, hg]
  calc
    x = fromS b * y * (fromS b)⁻¹ := by dsimp [y]; group
    _ = _ := by rw [he]; group

end Tits.AmalgamRigidity.FullRee.PointedPairs
