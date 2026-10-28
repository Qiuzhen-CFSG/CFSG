module

public import Theory.GroupAction.FiveOrbitBinaryCoordinates

/-!
# Sum-free five-orbits on elementary sixteen

The binary coordinates of a nonidentity orbit of a fixed-point-free order-five
action are the four unit vectors and their sum. Adding the first unit vector
to any of these five vectors never gives one of them. This finite calculation
shows that multiplying an orbit point by its base point leaves the orbit.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
the five-coset calculation on pp.673–676.
-/

open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupAction
/-- Multiplication by its base point takes a nonidentity five-orbit
outside itself. Equivalently, the five-point orbit is sum-free. -/
public theorem five_orbit_base_mul_not_mem {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction A V]
    (hA : Nat.card A = 5) (hV : Nat.card V = 16)
    (hfixed : FixedPoints.subgroup A V = ⊥)
    (b : V) (hb : b ≠ 1) :
    ∀ x ∈ MulAction.orbit A b, b * x ∉ MulAction.orbit A b := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let _ : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨g, hg⟩ := exists_ne (1 : A)
  obtain ⟨hrel, hinj, _⟩ := five_orbit_binary_coordinates hA hV hfixed b hb g hg
  let v : Fin 4 → V := fun i => g ^ i.val • b
  let w : (Fin 4 → Fin 2) → V := fun e =>
    v 0 ^ (e 0).val * v 1 ^ (e 1).val * v 2 ^ (e 2).val * v 3 ^ (e 3).val
  have hi : Function.Injective w := hinj
  have hsq (i : Fin 4) : v i * v i = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (v i)
  have hmul (e f : Fin 4 → Fin 2) : w (e + f) = w e * w f := by
    have hp (i : Fin 4) (a c : Fin 2) :
        v i ^ (a + c).val = v i ^ a.val * v i ^ c.val := by
      fin_cases a <;> fin_cases c <;> simp [hsq]
    simp only [w, Pi.add_apply, hp]
    ac_rfl
  let c : Fin 5 → (Fin 4 → Fin 2) :=
    ![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1], ![1,1,1,1]]
  have hc (i : Fin 5) : w (c i) = g ^ i.val • b := by
    fin_cases i <;> simp [w, c, v, hrel]
  have horb (x : V) (hx : x ∈ MulAction.orbit A b) : ∃ i, x = w (c i) := by
    obtain ⟨a, rfl⟩ := hx
    have ha : a ∈ zpowers g := by rw [zpowers_eq_top_of_prime_card hA hg]; trivial
    obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp ha)
    have ho : orderOf g = 5 := orderOf_eq_prime (by simpa [hA] using pow_card_eq_one' (x := g)) hg
    have hn5 : n < 5 := by simpa [ho] using hn
    exact ⟨⟨n, hn5⟩, by rw [hc, heq]⟩
  intro x hx hbx
  obtain ⟨i, rfl⟩ := horb x hx
  obtain ⟨j, hj⟩ := horb (b * w (c i)) hbx
  have hc0 : w (c 0) = b := by simpa using hc 0
  have he : c 0 + c i = c j := hi (by rw [hmul, hc0]; exact hj)
  have hne : ∀ i j : Fin 5, c 0 + c i ≠ c j := by decide +kernel
  exact hne i j he
end Theory.GroupAction
