module

public import Theory.Mathieu.M24.ValueBoundParabolics.Construction.Generators
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Order
public import Theory.Mathieu.M24.Properties.Simplicity
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple

/-!
# The three native parabolics generate M₂₄

Short explicit words in their generators have orders 3, 5, 7, 11, and 23.
Their join also contains the marked subgroup of order 1024. Coprime
divisibility bounds its index by 9. The faithful coset action of a proper
subgroup of the simple group M₂₄ would then embed M₂₄ in S₉, contradicting
its certified order. This proves generation without subgroup classification.

Source context: Aschbacher–Smith, E.4.3(2), printed p.242 (PDF p.253).
The small-index lemma is the existing attributed ATLAS port.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24ValueBoundParabolics.Construction
open M24LocalGeometry.SylowNormalizer

set_option maxRecDepth 100000

private noncomputable def jointGenerator : Fin 7 → M24 :=
  ![generator 0, generator 1, generator 2, generator 3, extra 0, extra 1, extra 2]

private def jointPoint : Fin 7 → Fin 24 → Fin 24 :=
  ![generatorPoint 0, generatorPoint 1, generatorPoint 2, generatorPoint 3,
    extraPoint 0, extraPoint 1, extraPoint 2]

private theorem jointGenerator_apply (a : Fin 7) (x : Fin 24) :
    (jointGenerator a).val x = jointPoint a x := by
  fin_cases a
  · exact generatorPerm_apply 0 x
  · exact generatorPerm_apply 1 x
  · exact generatorPerm_apply 2 x
  · exact generatorPerm_apply 3 x
  · rfl
  · rfl
  · rfl

private noncomputable def jointWord : List (Fin 7) → M24
  | [] => 1
  | a :: w => jointGenerator a * jointWord w

private def jointWordPoint : List (Fin 7) → Fin 24 → Fin 24
  | [], x => x
  | a :: w, x => jointPoint a (jointWordPoint w x)

private theorem jointWord_apply (w : List (Fin 7)) (x : Fin 24) :
    (jointWord w).val x = jointWordPoint w x := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change (jointGenerator a).val ((jointWord w).val x) = _
    rw [jointGenerator_apply, ih]
    rfl

private theorem jointWord_pow_apply (w : List (Fin 7)) (n : ℕ) (x : Fin 24) :
    (jointWord w ^ n).val x = (jointWordPoint w)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ]
    change (jointWord w ^ n).val ((jointWord w).val x) = _
    rw [ih, jointWord_apply]
    rfl

private noncomputable def join : Subgroup M24 := ⨆ i, parabolic i

private theorem jointGenerator_mem (a : Fin 7) : jointGenerator a ∈ join := by
  have hs : candidate ≤ join := (candidate_le_parabolic 0).trans (le_iSup (parabolic) 0)
  fin_cases a
  · exact hs (generator_mem 0)
  · exact hs (generator_mem 1)
  · exact hs (generator_mem 2)
  · exact hs (generator_mem 3)
  · exact (le_iSup parabolic 0) (extra_mem_parabolic 0)
  · exact (le_iSup parabolic 1) (extra_mem_parabolic 1)
  · exact (le_iSup parabolic 2) (extra_mem_parabolic 2)

private theorem jointWord_mem (w : List (Fin 7)) : jointWord w ∈ join := by
  induction w with
  | nil => exact join.one_mem
  | cons a w ih => exact join.mul_mem (jointGenerator_mem a) ih

private def prime : Fin 5 → ℕ := ![3,5,7,11,23]

private def primeWord : Fin 5 → List (Fin 7)
  | 0 => [4,0,4,0]
  | 1 => [6,6,4,6,6,4]
  | 2 => [4,5]
  | 3 => [2,5,4,6]
  | 4 => [6,0,4,6,5,4]

private theorem primeWord_order (i : Fin 5) : orderOf (jointWord (primeWord i)) = prime i := by
  let : Fact (prime i).Prime := ⟨(by decide +kernel : ∀ i, (prime i).Prime) i⟩
  apply orderOf_eq_prime
  · apply Subtype.ext
    apply Equiv.ext
    intro x
    change (jointWord (primeWord i) ^ prime i).val x = x
    rw [jointWord_pow_apply]
    exact (by decide +kernel : ∀ i x, (jointWordPoint (primeWord i))^[prime i] x = x) i x
  · intro h
    have hp := congrArg (fun g : M24 => g.val) h
    have he : ∀ x, jointWordPoint (primeWord i) x = x := by
      intro x
      rw [← jointWord_apply]
      exact congrArg (fun p : Equiv.Perm (Fin 24) => p x) hp
    exact (by decide +kernel : ∀ i, ¬ ∀ x, jointWordPoint (primeWord i) x = x) i he

private theorem prime_dvd_card (i : Fin 5) : prime i ∣ Nat.card join := by
  have h := orderOf_dvd_natCard (⟨jointWord (primeWord i), jointWord_mem _⟩ : join)
  simpa only [Subgroup.orderOf_mk, primeWord_order] using h

/-- The three concrete extensions generate the full native Witt-design group. -/
theorem parabolic_iSup : (⨆ i, parabolic i) = ⊤ := by
  let : IsSimpleGroup M24 := m24_isSimpleGroup
  have h1024 : 1024 ∣ Nat.card join := by
    simpa only [candidate_card, join] using Subgroup.card_dvd_of_le
      ((candidate_le_parabolic 0).trans (le_iSup parabolic 0))
  have h3 : 3 ∣ Nat.card join := prime_dvd_card 0
  have h5 : 5 ∣ Nat.card join := prime_dvd_card 1
  have h7 : 7 ∣ Nat.card join := prime_dvd_card 2
  have h11 : 11 ∣ Nat.card join := prime_dvd_card 3
  have h23 : 23 ∣ Nat.card join := prime_dvd_card 4
  have h3072 : 3072 ∣ Nat.card join :=
    (by decide +kernel : Nat.Coprime 3 1024).mul_dvd_of_dvd_of_dvd h3 h1024
  have h15360 : 15360 ∣ Nat.card join :=
    (by decide +kernel : Nat.Coprime 5 3072).mul_dvd_of_dvd_of_dvd h5 h3072
  have h107520 : 107520 ∣ Nat.card join :=
    (by decide +kernel : Nat.Coprime 7 15360).mul_dvd_of_dvd_of_dvd h7 h15360
  have h1182720 : 1182720 ∣ Nat.card join :=
    (by decide +kernel : Nat.Coprime 11 107520).mul_dvd_of_dvd_of_dvd h11 h107520
  have h27202560 : 27202560 ∣ Nat.card join :=
    (by decide +kernel : Nat.Coprime 23 1182720).mul_dvd_of_dvd_of_dvd h23 h1182720
  have hlo : 27202560 ≤ Nat.card join := Nat.le_of_dvd Nat.card_pos h27202560
  have hmul := join.card_mul_index
  rw [m24_order] at hmul
  have hi : join.index ≤ 9 := by nlinarith
  apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
  exact lt_of_le_of_lt (Nat.factorial_le hi) (by rw [m24_order]; decide +kernel)

end Sporadic.Mathieu.M24ValueBoundParabolics.Construction
