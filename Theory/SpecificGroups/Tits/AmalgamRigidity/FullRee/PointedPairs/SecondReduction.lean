module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.Core
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.SecondEmbedding

/-!
# Reduction to the linear Weyl fiber

An outside-Borel involution in the second binary Ree endpoint projects to one
of two involutions in its dihedral quotient of order six. An explicit element
of the core, fixed by the first Weyl action, exchanges those two fibers.
Consequently a fiber census with fixed-core conjugators gives the entire
second-endpoint census with the same constraint on its conjugators.

This is the quotient reduction for the pointed local calculation used in
Aschbacher--Smith F.4.8, printed p.278. The only finite verification here is
in the six-element quotient and on a single explicit core element.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.PointedPairs
open ReeTwo

def secondAnchor : Core := ⟨1,1,0,1,1,1,0,0,0,0⟩

theorem secondAnchor_fixed : Core.r secondAnchor = secondAnchor := by
  rw [← rPolynomial_eq]
  decide +kernel

theorem secondAnchor_quotient :
    (secondSylow (SemidirectProduct.inl secondAnchor)).right = DihedralGroup.sr 2 := rfl

theorem second_involution_conjugate_of_fiber (rep : ZMod 2 → SecondModel)
    (hfiber : ∀ y : SecondModel, y ^ 2 = 1 → y.right = DihedralGroup.sr 0 →
      ∃ g : Core, Core.r g = g ∧ ∃ e : ZMod 2,
        y = secondSylow (SemidirectProduct.inl g) * rep e *
          (secondSylow (SemidirectProduct.inl g))⁻¹)
    (y : SecondModel) (hy : y ^ 2 = 1) (hn : y ∉ secondSylow.range) :
    ∃ g : Core, Core.r g = g ∧ ∃ e : ZMod 2,
      y = secondSylow (SemidirectProduct.inl g) * rep e *
        (secondSylow (SemidirectProduct.inl g))⁻¹ := by
  have hyq : y.right ^ 2 = 1 := congrArg (SemidirectProduct.rightHom (φ := secondAction)) hy
  have hnq : ¬ (y.right = 1 ∨ y.right = DihedralGroup.sr 2) :=
    fun h => hn ((mem_secondB_iff y).mpr h)
  have he : y.right = DihedralGroup.sr 0 ∨ y.right = DihedralGroup.sr 1 :=
    (by decide +kernel : ∀ a : DihedralGroup 3, a^2=1 →
      ¬ (a=1 ∨ a=DihedralGroup.sr 2) →
      a=DihedralGroup.sr 0 ∨ a=DihedralGroup.sr 1) y.right hyq hnq
  rcases he with he | he
  · exact hfiber y hy he
  · let d := secondSylow (SemidirectProduct.inl secondAnchor)
    let v := d⁻¹ * y * d
    have hv : v^2=1 := by
      dsimp only [v]
      calc
        _ = d⁻¹*y^2*d := by simp only [pow_two]; group
        _ = 1 := by rw [hy]; group
    have hvq : v.right = DihedralGroup.sr 0 := by
      change d.right⁻¹ * y.right * d.right = DihedralGroup.sr 0
      change (secondSylow (SemidirectProduct.inl secondAnchor)).right⁻¹ * y.right *
        (secondSylow (SemidirectProduct.inl secondAnchor)).right = DihedralGroup.sr 0
      rw [secondAnchor_quotient, he]
      decide +kernel
    obtain ⟨g,hg,e,hge⟩ := hfiber v hv hvq
    refine ⟨secondAnchor * g, ?_, e, ?_⟩
    · rw [map_mul, secondAnchor_fixed, hg]
    · calc
        y = d * v * d⁻¹ := by dsimp only [v]; group
        _ = _ := by
          rw [hge, map_mul, map_mul]
          dsimp only [d]
          group

end Tits.AmalgamRigidity.FullRee.PointedPairs
