module
public import Theory.GroupTheory.QuaternionSwapModel.MarkedCubic
public import Theory.GroupTheory.FourWreathTwoCores

/-!
# Compatible coordinates for the binary four-group wreath product

The function and pair encodings of E₄ are identified by reversing their two
coordinates. This makes the quaternion cubic induce the cubic used by the
invariant-subgroup calculation. Applying the same map to both wreath factors
preserves the actor, the base, and the diagonal-plus-swap eight-group.

These are quotient coordinates only: the split quaternion-swap group and the
nonsplit Aut(M₁₂) first core can share this quotient without being isomorphic.
Source: Aschbacher--Smith, proof of 14.2.21, printed p.988, refs/quasithin.pdf.
-/

@[expose] public section
namespace QuaternionSwapModel.WreathCoordinates

/-- Reversing the binary coordinates aligns the two published cubic markings. -/
def fourEquiv : E4 ≃* FourWreathTwo.E4 where
  toFun v := Multiplicative.ofAdd (v.toAdd 1, v.toAdd 0)
  invFun v := Multiplicative.ofAdd ![v.toAdd.2, v.toAdd.1]
  left_inv v := by
    change (![v.toAdd 0, v.toAdd 1] : Fin 2 → ZMod 2) = v.toAdd
    funext i
    fin_cases i <;> rfl
  right_inv v := rfl
  map_mul' v w := rfl

/-- The wreath isomorphism fixes the actor and changes both planes by the same map. -/
def wreathEquiv : W ≃* FourWreathTwo.Wreath :=
  RegularWreathProduct.congr fourEquiv (MulEquiv.refl C2)

theorem wreathEquiv_left (w : W) (t : C2) :
    (wreathEquiv w).left t = fourEquiv (w.left t) := rfl

theorem wreathEquiv_right (w : W) : (wreathEquiv w).right = w.right := rfl

theorem mem_base (w : W) : wreathEquiv w ∈ FourWreathTwo.base ↔ w ∈ base := Iff.rfl

theorem mem_other (w : W) : wreathEquiv w ∈ FourWreathTwo.other ↔ w ∈ other := by
  rw [FourWreathTwo.mem_other_iff]
  change fourEquiv (w.left 1) = fourEquiv (w.left turn) ↔ w.left 1 = w.left turn
  exact fourEquiv.injective.eq_iff

theorem map_base : base.map wreathEquiv.toMonoidHom = FourWreathTwo.base := by
  ext w
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (mem_base x).mpr hx
  · intro hw
    obtain ⟨x,rfl⟩ := wreathEquiv.surjective w
    exact ⟨x,(mem_base x).mp hw,rfl⟩

theorem map_other : other.map wreathEquiv.toMonoidHom = FourWreathTwo.other := by
  ext w
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (mem_other x).mpr hx
  · intro hw
    obtain ⟨x,rfl⟩ := wreathEquiv.surjective w
    exact ⟨x,(mem_other x).mp hw,rfl⟩

theorem quaternion_cubic (q : QuaternionGroup 2) :
    fourEquiv (quaternionQuotient (GLS3.Chapter5.SchurPresentation.q8Cycle q)) =
      FourWreathTwo.cubicFour (fourEquiv (quaternionQuotient q)) := by
  have h : ∀ q : QuaternionGroup 2,
      fourEquiv (quaternionQuotient (GLS3.Chapter5.SchurPresentation.q8Cycle q)) =
        FourWreathTwo.cubicFour (fourEquiv (quaternionQuotient q)) := by decide +kernel
  exact h q

theorem cycle_equivariant (x : QH) :
    wreathEquiv (wreathMap (MarkedCubic.cycle x)) =
      FourWreathTwo.cubic (wreathEquiv (wreathMap x)) := by
  obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter x
  apply RegularWreathProduct.ext
  · funext t
    exact quaternion_cubic (r.left t)
  · rfl

end QuaternionSwapModel.WreathCoordinates
