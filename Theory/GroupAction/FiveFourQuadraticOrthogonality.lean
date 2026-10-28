module

public import Theory.GroupAction.FiveFourBinaryModel
public import Theory.GroupAction.FiveFourBinaryCoordinates

/-!
# Transport of five-four quadratic orthogonality

Compatible coordinates identify the two elementary groups and their dual
pairing with the even subsets of the five-element affine line. Transporting
the square map preserves quadraticity, equivariance, self-orthogonality and
its additional zero. The finite-model theorem then gives the required
orthogonality to a preimage of the involution displacement.
For faithful five-four actions on groups of order sixteen, compatible
coordinates exist for every supplied order-four actor, giving the assertion
without any coordinate hypothesis.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and p.678 preceding equation (2).
-/

namespace Theory.GroupAction.BinaryQuadraticPairing
open FiveFourBinaryModel

/-- The square-displacement assertion after compatible action coordinates
have been constructed. -/
public theorem square_displacement_orthogonality_of_coordinates
    {A V W : Type*} [Group A] [Group V] [Group W]
    (d : BinaryQuadraticPairing A V W) (g : A) (c : Coordinates d g)
    (b : V) (w : W)
    (heq : d.square b = d.rightAction (g ^ 2) w * w)
    (hne : d.square b ≠ 1) : d.pairing b w = 1 := by
  let q : Space → Space := fun x => c.right (d.square (c.left.symm x))
  have hqt (x : Space) : q (translate x) = translate (q x) := by
    have hx : c.left.symm (translate x) = d.leftAction c.translationActor (c.left.symm x) := by
      apply c.left.injective
      simp only [c.left.apply_symm_apply, c.left_translate]
    dsimp [q]
    rw [hx, d.square_equivariant, c.right_translate]
  have hqs (x : Space) : q (turn x) = turn (q x) := by
    have hx : c.left.symm (turn x) = d.leftAction c.turnActor (c.left.symm x) := by
      apply c.left.injective
      simp only [c.left.apply_symm_apply, c.left_turn]
    dsimp [q]
    rw [hx, d.square_equivariant, c.right_turn]
  have hq1 : q 1 = 1 := by simp [q, d.square_one]
  have hqq (x y z : Space) : q (x * y * z) * q (x * y) * q (x * z) *
      q (y * z) * q x * q y * q z = 1 := by
    simpa only [q, map_mul, map_one] using
      congrArg c.right (d.square_quadratic (c.left.symm x) (c.left.symm y) (c.left.symm z))
  have hself (x : Space) : FiveFourBinaryModel.pairing x (q x) = 1 := by
    have hh := d.square_self (c.left.symm x)
    rw [c.pairing_eq, c.left.apply_symm_apply] at hh
    exact hh
  have hzero : ∃ x, x ≠ 1 ∧ q x = 1 := by
    obtain ⟨x, hx, hqx⟩ := d.square_has_nontrivial_zero
    refine ⟨c.left x, ?_, ?_⟩
    · exact fun h => hx (c.left.injective (h.trans (map_one c.left).symm))
    · simp [q, hqx]
  have hdisp : q (c.left b) = turn (turn (c.right w)) * c.right w := by
    simpa only [q, c.left.symm_apply_apply, map_mul, c.right_square] using congrArg c.right heq
  have hn : q (c.left b) ≠ 1 := by
    dsimp [q]
    rw [c.left.symm_apply_apply]
    exact fun h => hne (c.right.injective (h.trans (map_one c.right).symm))
  rw [c.pairing_eq]
  exact FiveFourBinaryModel.square_displacement_orthogonality q hq1 hqt hqs hqq hself hzero
    (c.left b) (c.right w) hdisp hn

/-- For a faithful five-four action on paired elementary groups of order sixteen,
a nonidentity square that is an involution displacement is orthogonal to its
displacement preimage. The square map's nonidentity zero is supplied by `d`. -/
public theorem square_displacement_orthogonality
    {V W : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hV : Nat.card V = 16) (hW : Nat.card W = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (d : BinaryQuadraticPairing
      (Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) V W)
    (g : Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) (hg : orderOf g = 4)
    (b : V) (w : W)
    (heq : d.square b = d.rightAction (g ^ 2) w * w)
    (hne : d.square b ≠ 1) : d.pairing b w = 1 := by
  obtain ⟨c⟩ := d.exists_five_four_coordinates hV hW φ hφ g hg
  exact d.square_displacement_orthogonality_of_coordinates g c b w heq hne

end Theory.GroupAction.BinaryQuadraticPairing
