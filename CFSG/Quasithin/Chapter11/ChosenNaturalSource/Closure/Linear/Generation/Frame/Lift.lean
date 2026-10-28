module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame.Hall
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Mathlib.GroupTheory.Nilpotent
open Subgroup Subgroup.OddHall
public section

/-!
# Exact lifts of the Weyl elements

Hall conjugacy is applied in the preimage of the actual Cartan image.
Its correction can have nontrivial image. Multiplication by an element
of the original Cartan cancels this image, producing an exact lift.
Consequently its action on every selected field line is unchanged.
This is the lift step in Aschbacher–Smith 11.5.7, printed p.781.
-/

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame
variable {A B : Type*} [Group A] [Finite A] [Group B]
/-- Correct in the Cartan-image preimage, then remove the image of the correction
with an element of the original Cartan. The final lift has exactly the prescribed image. -/
theorem exists_normalizer_lift (f : A →* B) (hf : Function.Surjective f)
    (X : Subgroup A) (ho : Odd (Nat.card X)) (hk : IsPGroup 2 f.ker)
    (hs : Group.IsSolvable (X.map f)) {b : B}
    (hb : b ∈ normalizer (X.map f : Set B)) :
    ∃ a : A, a ∈ normalizer (X : Set A) ∧ f a = b := by
  let N := (X.map f).comap f
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  let : Group.IsSolvable (X.map f) := hs
  have hN : Group.IsSolvable N := isSolvable_comap_of_solvable_ker f (X.map f)
  obtain ⟨a, ha⟩ := hf b
  let Y := X.map (MulAut.conj a).toMonoidHom
  have hY : Y.map f = X.map f := by
    have he : Y.map f = (X.map f).map (MulAut.conj b).toMonoidHom := by
      rw [map_map, map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, ha]
    exact he.trans (mem_normalizer_iff_map_conj_eq.mp hb)
  have hXN : X ≤ N := le_comap_map f X
  have hYN : Y ≤ N := by
    change Y ≤ (X.map f).comap f
    rw [← hY]
    exact le_comap_map f Y
  have hsupX : f.ker ⊔ X = N := by
    rw [sup_comm]
    exact (comap_map_eq f X).symm
  have hsupY : f.ker ⊔ Y = N := by
    rw [sup_comm, ← comap_map_eq, hY]
  have hho : Odd (Nat.card Y) := by
    rw [card_map_of_injective (MulAut.conj a).injective]
    exact ho
  have hHallX : IsHallSubgroup oddPrimes (X.subgroupOf N) :=
    oddHall_of_normalized_sup hk ho.coprime_two_left
      (by rw [f.ker.normalizer_eq_top]; exact le_top) hsupX
  have hHallY : IsHallSubgroup oddPrimes (Y.subgroupOf N) :=
    oddHall_of_normalized_sup hk hho.coprime_two_left
      (by rw [f.ker.normalizer_eq_top]; exact le_top) hsupY
  obtain ⟨c, hc⟩ := exists_normalizer_correction hN hXN hYN hHallX hHallY
  obtain ⟨z, hz, hzc⟩ := (show f (c : A) ∈ X.map f from c.property)
  refine ⟨z * ((c : A)⁻¹ * a),
    (normalizer (X : Set A)).mul_mem (X.le_normalizer hz) hc, ?_⟩
  simp only [map_mul, map_inv, hzc, mul_inv_cancel_left, ha]
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame
