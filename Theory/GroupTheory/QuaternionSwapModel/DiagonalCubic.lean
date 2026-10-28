module
public import Theory.GroupTheory.QuaternionSwapModel.Parabolic
public import Theory.GroupTheory.QuaternionSwapModel.MarkedCubic
public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut

/-!
# Arbitrary diagonal cubics in the quaternion-swap model

Every nontrivial quaternion automorphism of order three preserves the
model's elementary sixteen and moves its marked plane. The movement follows
because a cubic quaternion automorphism fixes no noncentral coset modulo
the center. A factor-and-swap extensionality lemma retains the actual model
embedding when applying this fact to an ambient cubic actor.

Source: Aschbacher--Smith, Lemma 14.2.21, printed p.988.
-/

public section
open Subgroup
namespace QuaternionSwapModel
open MarkedCubic

/-- Every nontrivial cubic diagonal action moves the marked plane. -/
theorem qhAut_moves_markedPlane (a : MulAut (QuaternionGroup 2))
    (ha : a ^ 3 = 1) (hne : a ≠ 1) :
    markedPlane.map (qhAut a).toMonoidHom ≠ markedPlane := by
  intro he
  have hj : projection (diagonalRaw (QuaternionGroup.xa 0)) ∈ markedPlane := by
    rw [markedPlane_eq_closure]
    exact subset_closure (Set.mem_insert_of_mem _ rfl)
  have hh := mem_map_of_mem (qhAut a).toMonoidHom hj
  rw [he] at hh
  change qhAut a (projection (diagonalRaw (QuaternionGroup.xa 0))) ∈ markedPlane at hh
  rw [qhAut_diag] at hh
  obtain ⟨v,hv,hvx⟩ := hh
  change projection (sixteenRaw v) = projection (diagonalRaw (a (QuaternionGroup.xa 0))) at hvx
  rw [projection_eq_iff] at hvx
  have hsq : (a (QuaternionGroup.xa 0)) ^ 2 ≠ 1 := by
    intro h
    have hn : (QuaternionGroup.xa 0 : QuaternionGroup 2)^2 ≠ 1 := by decide
    apply hn
    apply a.injective
    simpa only [map_pow,map_one] using h
  have hcalc : ∀ (v : E16) (q : QuaternionGroup 2), v ∈ planeCoordinates →
      ((sixteenRaw v)⁻¹ * diagonalRaw q = 1 ∨ (sixteenRaw v)⁻¹ * diagonalRaw q = killed) →
      q ^ 2 ≠ 1 → (QuaternionGroup.xa 0)⁻¹ * q ∈ center (QuaternionGroup 2) := by
    decide +kernel
  have hc := QuaternionGroup.mem_center_of_central_difference_of_cube_eq_one_ne_one
    a ha hne (hcalc v _ hv hvx hsq)
  have hn : QuaternionGroup.xa 0 ∉ center (QuaternionGroup 2) := by decide
  exact hn hc

/-- Homomorphisms out of the swap model are determined by its literal factors and swap. -/
theorem hom_ext_factors_swap {D : Type*} [Group D] (f g : QH →* D)
    (hL : ∀ q, f (leftEmbedding q) = g (leftEmbedding q))
    (hR : ∀ q, f (rightEmbedding q) = g (rightEmbedding q))
    (hs : f swap = g swap) : f = g := by
  apply MonoidHom.ext
  intro x
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter x
  have hd : w = leftRaw (w.left 1) * rightRaw (w.left turn) * swapRaw ^ w.right.toAdd.val := by
    have hh : ∀ w : Raw,
      w = leftRaw (w.left 1) * rightRaw (w.left turn) * swapRaw ^ w.right.toAdd.val := by
      decide +kernel
    exact hh w
  rw [hd,map_mul,map_mul,map_pow,map_mul,map_mul,map_pow,map_mul,map_mul,map_pow]
  change f (leftEmbedding _) * f (rightEmbedding _) * f swap ^ _ =
    g (leftEmbedding _) * g (rightEmbedding _) * g swap ^ _
  rw [hL,hR,hs]

end QuaternionSwapModel
