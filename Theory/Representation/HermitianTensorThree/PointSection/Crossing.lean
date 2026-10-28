module
public import Theory.Representation.HermitianTensorThree.PointSection.Movement

/-!
# Crossing the marked point and plane in the Hermitian nine-space

If an inner congruence sends the central point into the selected hyperplane,
its lower first-column entry vanishes. The same entry calculation sends the
whole point-radical commutator five-space into that hyperplane. Thus independent
point and plane markings can be compared without replacing either subgroup.

Source: Aschbacher–Smith H.4.6(5), used in 8.2.12, printed pp.382,722,
refs/quasithin.pdf. The Chapter 8 and 12 crossing modules apply this to the
original selected pair and original central involution.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.HermitianTensorThree.PointSection

/-- A conjugate point in the selected plane has its entire tangent five-space
in the selected hyperplane. The two markings need not have been chosen together. -/
theorem moved_image_hyperplane (a : binaryImage 1)
    (ha : (a.val pointVector).val 2 2 = 0) (X : Space 1) (hX : X ∈ moved) :
    (a.val X).val 2 2 = 0 := by
  obtain ⟨b,heq⟩ := a.property
  rw [←heq] at ha ⊢
  have hb : b 2 0 = 0 := by
    have he : b 2 0 * sigma 1 (b 2 0) = 0 := by
      change (b.val * pointVector.val * adjoint 1 b.val) 2 2 = 0 at ha
      simpa [pointVector,coordinates,adjoint,Matrix.mul_apply,Fin.sum_univ_three] using ha
    exact (mul_eq_zero.mp he).elim id (fun hz => (sigma 1).injective
      (hz.trans (map_zero _).symm))
  obtain ⟨h11,h22,h12⟩ := (mem_moved X).mp hX
  have h21 : X.val 2 1 = 0 := by
    rw [←entry_conjugate 1 X 2 1,h12,map_zero]
  change (b.val * X.val * adjoint 1 b.val) 2 2 = 0
  simp [Matrix.mul_apply,Fin.sum_univ_three,adjoint,hb,h11,h22,h12,h21]

end Representation.HermitianTensorThree.PointSection
