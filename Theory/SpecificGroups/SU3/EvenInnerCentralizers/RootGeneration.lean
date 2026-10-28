module

public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Binary Hermitian root generation by a norm-one torus

The root coordinates satisfy `b + conj b + a * conj a = 0`; their group
law is the Hermitian Heisenberg law, not the unrestricted unitriangular law.
A norm-one torus acts on the first coordinate by its cube. A normal subgroup
containing an actor with nontrivial cube therefore covers every first
coordinate. Squares and surjectivity of the field norm then supply the whole
central layer, giving containment of the entire root group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the inner
unitary case in the proof of 16.4.8, printed p.1188. Coordinates and the
torus action are those of Huppert II.10.12.
-/

public section
open BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenInner
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- The first-coordinate map of the actual Hermitian Heisenberg group. -/
def first : hermitianUnipotentCoord J →* Multiplicative E where
  toFun z := Multiplicative.ofAdd z.val.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Every first coordinate occurs, by surjectivity of the quadratic trace. -/
theorem first_surjective [Finite E] {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    Function.Surjective (first J) := by
  intro a
  obtain ⟨b, hb⟩ := huppert_II_10_4_trace_surjective J q hcard hfixed
    (-(a.toAdd * J.conj a.toAdd)) (by
      rw [map_neg, map_mul, J.conj_involutive, mul_comm])
  exact ⟨⟨(a.toAdd, b), by dsimp only; rw [hb]; ring⟩, rfl⟩

/-- In characteristic two, squares fill the central root layer through the norm. -/
theorem square_coordinates [CharP E 2] (z : hermitianUnipotentCoord J) :
    (z ^ 2).val = (0, z.val.1 * J.conj z.val.1) := by
  rw [pow_two]
  change (z.val.1 + z.val.1, z.val.2 + z.val.2 - z.val.1 * J.conj z.val.1) = _
  simp [CharTwo.add_self_eq_zero, CharTwo.neg_eq]

/-- A subgroup covering the first coordinate contains the entire root group.
The central layer is recovered by squares, so no normality is needed here. -/
theorem range_le_of_first_surjective [Finite E] [CharP E 2] {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    {G : Type*} [Group G] (f : hermitianUnipotentCoord J →* G)
    (N : Subgroup G)
    (hfirst : ∀ a : E, ∃ z : hermitianUnipotentCoord J,
      z.val.1 = a ∧ f z ∈ N) : f.range ≤ N := by
  have hcentral (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) : f z ∈ N := by
    by_cases hb : z.val.2 = 0
    · have he : z = 1 := Subtype.ext (Prod.ext hz hb)
      simpa only [he, map_one] using N.one_mem
    · have hfix : J.conj z.val.2 = z.val.2 := by
        have hp := z.property
        rw [hz, zero_mul, add_zero] at hp
        exact (eq_neg_of_add_eq_zero_right hp).trans (CharTwo.neg_eq _)
      obtain ⟨a, _, ha⟩ := huppert_II_10_4_norm_surjective J q hcard hfixed
        z.val.2 hfix hb
      obtain ⟨w, hw, hwN⟩ := hfirst a
      have hs : w ^ 2 = z := by
        apply Subtype.ext
        rw [square_coordinates, hw, ha]
        exact Prod.ext hz.symm rfl
      rw [← hs, map_pow]
      exact N.pow_mem hwN 2
  rintro _ ⟨z, rfl⟩
  obtain ⟨w, hw, hwN⟩ := hfirst z.val.1
  have hz : (z * w⁻¹).val.1 = 0 := by
    change z.val.1 + -w.val.1 = 0
    rw [hw, add_neg_cancel]
  have hh := N.mul_mem (hcentral (z * w⁻¹) hz) hwN
  simpa only [map_mul, map_inv, inv_mul_cancel_right] using hh

/-- On the first coordinate the norm-one torus has weight three. -/
theorem normOne_action_first (k : Eˣ)
    (hk : J.conj (k : E) = (k : E)⁻¹) (z : hermitianUnipotentCoord J) :
    (hermitianTorusAction J k z).val.1 = (k : E) ^ 3 * z.val.1 := by
  rw [hermitianTorusAction_fst, hk, inv_inv]
  ring

/-- A norm-one torus fixes the second root coordinate. -/
theorem normOne_action_second (k : Eˣ)
    (hk : J.conj (k : E) = (k : E)⁻¹) (z : hermitianUnipotentCoord J) :
    (hermitianTorusAction J k z).val.2 = z.val.2 := by
  rw [hermitianTorusAction_snd, hk, inv_inv]
  simp

/-- A nontrivial cubic torus action forces the whole Hermitian root group
into a normal subgroup containing the actor, including the central layer. -/
theorem root_le_normal [Finite E] [CharP E 2] {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    {G : Type*} [Group G] (f : hermitianUnipotentCoord J →* G)
    (N : Subgroup G) [N.Normal] (t : G) (ht : t ∈ N)
    (k : Eˣ) (hk : J.conj (k : E) = (k : E)⁻¹)
    (hk3 : (k : E) ^ 3 ≠ 1)
    (hact : ∀ z, t * f z * t⁻¹ = f (hermitianTorusAction J k z)) :
    f.range ≤ N := by
  apply range_le_of_first_surjective J hcard hfixed f N
  intro a
  obtain ⟨z, hz⟩ := first_surjective J hcard hfixed
    (Multiplicative.ofAdd (a / ((k : E) ^ 3 - 1)))
  have hz' : z.val.1 = a / ((k : E) ^ 3 - 1) := congrArg Multiplicative.toAdd hz
  refine ⟨hermitianTorusAction J k z * z⁻¹, ?_, ?_⟩
  · change (hermitianTorusAction J k z).val.1 + -z.val.1 = a
    rw [normOne_action_first J k hk, hz']
    field_simp [sub_ne_zero.mpr hk3]
    ring
  · have hh := (inferInstance : N.Normal).conj_mem t⁻¹ (N.inv_mem ht) (f z)
    have hm := N.mul_mem ht hh
    have he : t * (f z * t⁻¹ * (f z)⁻¹) =
        f (hermitianTorusAction J k z * z⁻¹) := by
      rw [map_mul, map_inv, ← hact]
      group
    rwa [he] at hm

/-- A prime-power-order actor supplies the normal subgroup needed above. -/
theorem root_le_primeToResidual [Finite E] [CharP E 2] {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    {G : Type*} [Group G] (f : hermitianUnipotentCoord J →* G)
    (p : ℕ) (t : G) {r : ℕ} (ht : t ^ (p ^ r) = 1)
    (k : Eˣ) (hk : J.conj (k : E) = (k : E)⁻¹)
    (hk3 : (k : E) ^ 3 ≠ 1)
    (hact : ∀ z, t * f z * t⁻¹ = f (hermitianTorusAction J k z)) :
    f.range ≤ Subgroup.primeToResidual p G :=
  root_le_normal J hcard hfixed f _ t (Subgroup.mem_primeToResidual_of_pow ht)
    k hk hk3 hact

/-- The action equation used above is the actual projective matrix action. -/
theorem projective_torus_action
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (k : Eˣ) (z : hermitianUnipotentCoord J) :
    hermitianTorusPSU J hJ k * hermitianUnipotentPSU J hJ z *
      (hermitianTorusPSU J hJ k)⁻¹ =
        hermitianUnipotentPSU J hJ (hermitianTorusAction J k z) := by
  rw [hermitianTorusPSU_mul_unipotent, mul_inv_cancel_right]

end BenderSuzuki.MatrixGroups.HermitianForm.EvenInner
