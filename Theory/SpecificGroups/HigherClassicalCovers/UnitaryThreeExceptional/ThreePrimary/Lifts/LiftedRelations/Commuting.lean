module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Lifts.LiftedRelations.Geometry
public import Theory.GroupTheory.CentralExtensionSwap
import Mathlib.Tactic.FinCases

/-!
# Exact commutations among lifted unitary roots

Partial inversion gives six commuting pairs in every central extension. The
long-root swap gives a seventh. The middle short plane commutes because its
first coordinate is, up to the highest root, a commutator of two elements
centralized projectively by the second coordinate. Moving this plane by the
explicit unitary Weyl element also makes the first short plane commute.

Thus nine of the fifteen collection relations hold exactly, with no assumption
on the kernel order or exponent. In particular the previously proposed
`shortDefect` is always trivial; it cannot supply the second exceptional
defect. Source: the root calculation underlying Aschbacher--Smith I.1.4(5),
printed p.408, and GLS3 §6.1.
-/

public noncomputable section
open scoped commutatorElement
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts
namespace LiftedRelations

variable {E : Type*} [Group E] (f : E →* S) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (L : CubicRootLifts f)

include hk in
private theorem commute_of_images {x y x' y' : E}
    (hx : f x = f x') (hy : f y = f y') (h : Commute x' y') : Commute x y := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [CentralExtension.commutator_eq_of_image_eq f hk hx hy]
  exact h.commutator_eq

private theorem root_commute (i j : Fin 6) (hij : i < j)
    (ht : swapTail root i j = 1) : Commute (root i) (root j) := by
  change root i * root j = root j * root i
  simpa only [ht, mul_one] using (root_swap i j hij).symm

include hf hk in
/-- The short-root inverter separates these six commuting pairs. -/
theorem commute_partial (i j : Fin 6)
    (hij : (i = 0 ∧ j = 5) ∨ (i = 1 ∧ j = 5) ∨
      (i = 2 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨
      (i = 3 ∧ j = 5) ∨ (i = 4 ∧ j = 5)) : Commute (L.gen i) (L.gen j) := by
  have aux (r s : Fin 6) (hr : inverterIndex r = 0) (hs : s = 2 ∨ s = 5)
      (hrs : Commute (root r) (root s)) : Commute (L.gen r) (L.gen s) := by
    apply CentralExtension.commute_lifts_of_partial_inversion f hf hk
      (root r) (root s) (torus 0) (n := 3) (by decide) (root_cube r) hrs
      (by simpa only [hr] using torus_inverts r) (torus_fixes_long s hs)
      _ _ (L.projects r) (L.projects s)
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact aux 0 5 rfl (Or.inr rfl) (root_commute 0 5 (by decide) (by simp [swapTail]))
  · exact aux 1 5 rfl (Or.inr rfl) (root_commute 1 5 (by decide) (by simp [swapTail]))
  · exact (aux 3 2 rfl (Or.inl rfl)
      (root_commute 2 3 (by decide) (by simp [swapTail])).symm).symm
  · exact (aux 4 2 rfl (Or.inl rfl)
      (root_commute 2 4 (by decide) (by simp [swapTail])).symm).symm
  · exact aux 3 5 rfl (Or.inr rfl) (root_commute 3 5 (by decide) (by simp [swapTail]))
  · exact aux 4 5 rfl (Or.inr rfl) (root_commute 4 5 (by decide) (by simp [swapTail]))

include hf hk in
/-- Swapping the two long roots kills their lifted commutator. -/
theorem commute_long : Commute (L.gen 2) (L.gen 5) := by
  obtain ⟨t, ht2, ht5⟩ := exists_long_swap
  exact CentralExtension.commute_lifts_of_swap f hf hk (root 2) (root 5) t
    (n := 3) (by decide) (root_cube 2)
    (root_commute 2 5 (by decide) (by simp [swapTail])) ht2 ht5
    _ _ (L.projects 2) (L.projects 5)

include hk in
private theorem commute_commutator_of_image_commute (x y z : E)
    (hy : Commute (f x) (f y)) (hz : Commute (f x) (f z)) : Commute x ⁅y,z⁆ := by
  apply (mul_inv_eq_iff_eq_mul).mp
  rw [conjugate_commutatorElement]
  apply CentralExtension.commutator_eq_of_image_eq f hk
  · rw [map_mul, map_mul, map_inv, hy.eq, mul_inv_cancel_right]
  · rw [map_mul, map_mul, map_inv, hz.eq, mul_inv_cancel_right]

private theorem root_commutator_one_two : ⁅root 1, root 2⁆ = root 3 ^ 2 * root 5 := by
  have h : ⁅rootSU 1, rootSU 2⁆ = rootSU 3 ^ 2 * rootSU 5 := by
    apply Subtype.ext
    apply Units.ext
    change rootMatrix 1 * rootMatrix 2 * (rootMatrix 1 ^ 2) * (rootMatrix 2 ^ 2) =
      rootMatrix 3 ^ 2 * rootMatrix 5
    decide +kernel
  simpa only [map_commutatorElement, map_mul, map_pow, root] using
    congrArg coordinateProjection h

include hf hk in
/-- The derived short-root plane has commuting lifts. -/
theorem commute_middle : Commute (L.gen 3) (L.gen 4) := by
  have hc : Commute (L.gen 4) ⁅L.gen 1, L.gen 2⁆ :=
    commute_commutator_of_image_commute f hk _ _ _
      (by rw [L.projects, L.projects]
          exact (root_commute 1 4 (by decide) (by simp [swapTail])).symm)
      (by rw [L.projects, L.projects]
          exact (root_commute 2 4 (by decide) (by simp [swapTail])).symm)
  have hm : f (L.gen 3 ^ 2 * L.gen 5) = f ⁅L.gen 1, L.gen 2⁆ := by
    rw [map_mul, map_pow, map_commutatorElement, L.projects, L.projects,
      L.projects, L.projects, root_commutator_one_two]
  have hp := commute_of_images f hk rfl hm hc
  have h5 : Commute (L.gen 4) (L.gen 5) := commute_partial f hf hk L 4 5 (by tauto)
  have h2 : Commute (L.gen 4) (L.gen 3 ^ 2) := by
    simpa only [mul_inv_cancel_right] using hp.mul_right h5.inv_right
  have hpow : L.gen 3 ^ 2 = (L.gen 3)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, L.cubes]
  rw [hpow] at h2
  simpa only [inv_inv] using h2.inv_right.symm

include hf hk in
/-- Conjugacy of the two short planes kills the first short commutator as well. -/
theorem commute_short : Commute (L.gen 0) (L.gen 1) := by
  obtain ⟨t, ht0, ht1⟩ := exists_short_move
  obtain ⟨T, hT⟩ := hf t
  have h : Commute (T * L.gen 0 * T⁻¹) (T * L.gen 1 * T⁻¹) := by
    apply commute_of_images f hk (x' := L.gen 4 ^ 2) (y' := L.gen 3)
    · rw [map_mul, map_mul, map_inv, map_pow, hT, L.projects, L.projects, ht0]
    · rw [map_mul, map_mul, map_inv, hT, L.projects, L.projects, ht1]
    · exact (commute_middle f hf hk L).symm.pow_left 2
  apply commutatorElement_eq_one_iff_commute.mp
  apply (MulAut.conj T).injective
  rw [map_one]
  change T * ⁅L.gen 0, L.gen 1⁆ * T⁻¹ = 1
  rw [conjugate_commutatorElement]
  exact h.commutator_eq

include hf hk in
/-- The first candidate defect from `Normalized` is identically one. -/
theorem shortDefect_eq_one : L.shortDefect = 1 := (commute_short f hf hk L).commutator_eq

/-- Exactly the nine pairs for which the lifted swap holds without a defect. -/
@[expose] def ExactPair (i j : Fin 6) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 5) ∨ (i = 1 ∧ j = 5) ∨
  (i = 2 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨ (i = 2 ∧ j = 5) ∨
  (i = 3 ∧ j = 4) ∨ (i = 3 ∧ j = 5) ∨ (i = 4 ∧ j = 5)

include hf hk in
theorem commute_exactPair (i j : Fin 6) (hij : ExactPair i j) :
    Commute (L.gen i) (L.gen j) := by
  rcases hij with ⟨rfl, rfl⟩ | h
  · exact commute_short f hf hk L
  rcases h with h | h | h | h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h | h
  · exact commute_partial f hf hk L i j (by tauto)
  · exact commute_partial f hf hk L i j (by tauto)
  · exact commute_partial f hf hk L i j (by tauto)
  · exact commute_partial f hf hk L i j (by tauto)
  · exact commute_long f hf hk L
  · exact commute_middle f hf hk L
  · exact commute_partial f hf hk L i j (by tauto)
  · exact commute_partial f hf hk L i j (by tauto)

end LiftedRelations
end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts
