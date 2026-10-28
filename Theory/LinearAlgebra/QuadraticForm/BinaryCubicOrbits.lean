module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Five cubic orbits and the M₁₂ square census

Two copies of the irreducible binary plane have five nonzero orbits of
length three. The first three representatives have both coordinates nonzero;
the last two are the two quaternion axes. The seven-term quadratic identity
forces the sum of the five orbit values to vanish. Hence an invariant quadratic
form has 0, 6 or 12 nonzero values, excluding the counts 3 and 9.

In the M₁₂ marking, the first two orbits represent noncentral involutions,
the third central involutions, and the last two elements of order four.
Equal values on the first two orbits and vanishing on the third and fourth
force vanishing on the fifth. The Chapter I application connects this
calculation to an actual central cover; the coordinate calculation alone
does not identify that cover.

Source: Aschbacher–Smith, I.2.2(5), printed p.412 / PDF p.423,
combined manuscript of 1 March 2004.
-/

@[expose] public section
namespace Theory.LinearAlgebra.BinaryCubicOrbits
abbrev Plane := ZMod 2 × ZMod 2
abbrev Space := Plane × Plane

def cubic (x : Space) : Space := ((x.1.2, x.1.1 + x.1.2), (x.2.2, x.2.1 + x.2.2))
def rep (j : Fin 5) : Space :=
  ![((1,0),(1,0)), ((1,0),(0,1)), ((1,0),(1,1)), ((1,0),(0,0)), ((0,0),(1,0))] j

def orbit (j : Fin 5) (k : Fin 3) : Space :=
  ![rep j, cubic (rep j), cubic (cubic (rep j))] k

def decode : Option (Fin 5 × Fin 3) → Space
  | none => 0
  | some (j,k) => orbit j k

theorem decode_bijective : Function.Bijective decode := by decide +kernel
noncomputable def orbitEquiv : Option (Fin 5 × Fin 3) ≃ Space :=
  Equiv.ofBijective decode decode_bijective

theorem orbit_invariant (q : Space → ZMod 2) (hi : ∀ x, q (cubic x) = q x)
    (j : Fin 5) (k : Fin 3) : q (orbit j k) = q (rep j) := by
  fin_cases k <;> simp [orbit, hi]

/-- The quadratic identity gives even parity on the five orbit values. -/
theorem parity (q : QuadraticForm (ZMod 2) Space) (hi : ∀ x, q (cubic x) = q x) :
    q (rep 0) + q (rep 1) + q (rep 2) + q (rep 3) + q (rep 4) = 0 := by
  have h := q.map_add_add_add_map ((1,0),(0,0)) ((0,1),(0,0)) ((0,0),(1,0))
  have hxyz : (((1,0),(0,0)) : Space) + ((0,1),(0,0)) + ((0,0),(1,0)) = orbit 1 2 := by decide +kernel
  have hxy : (((1,0),(0,0)) : Space) + ((0,1),(0,0)) = orbit 3 2 := by decide +kernel
  have hzx : (((0,0),(1,0)) : Space) + ((1,0),(0,0)) = rep 0 := by decide +kernel
  have hyz : (((0,1),(0,0)) : Space) + ((0,0),(1,0)) = orbit 2 1 := by decide +kernel
  have hy : (((0,1),(0,0)) : Space) = orbit 3 1 := by decide +kernel
  rw [hxyz, hxy, hzx, hyz, hy] at h
  simp only [orbit_invariant q hi] at h
  change q (rep 1) + (q (rep 3) + q (rep 3) + q (rep 4)) =
    q (rep 3) + q (rep 2) + q (rep 0) at h
  have binary : ∀ a b c d e : ZMod 2,
      b + (d + d + e) = d + c + a → a + b + c + d + e = 0 := by decide +kernel
  exact binary _ _ _ _ _ h

private def profileValue (c : Fin 5 → ZMod 2) : Option (Fin 5 × Fin 3) → ZMod 2
  | none => 0
  | some (j,_) => c j

private def profileCount (c : Fin 5 → ZMod 2) : ℕ :=
  Fintype.card {o : Option (Fin 5 × Fin 3) // profileValue c o ≠ 0}

noncomputable def nonzeroCount (q : Space → ZMod 2) : ℕ := Nat.card {v // q v ≠ 0}

private theorem count_eq_profile (q : QuadraticForm (ZMod 2) Space)
    (hi : ∀ x, q (cubic x) = q x) :
    nonzeroCount q = profileCount (fun j => q (rep j)) := by
  have he (o : Option (Fin 5 × Fin 3)) :
      profileValue (fun j => q (rep j)) o = q (orbitEquiv o) := by
    rcases o with _ | ⟨j,k⟩
    · exact q.map_zero.symm
    · exact (orbit_invariant q hi j k).symm
  have hcard := Nat.card_congr (orbitEquiv.subtypeEquiv
    (p := fun o => profileValue (fun j => q (rep j)) o ≠ 0)
    (q := fun v => q v ≠ 0) (fun o => by rw [← he o]))
  exact hcard.symm.trans Nat.card_eq_fintype_card

theorem count_cases (q : QuadraticForm (ZMod 2) Space)
    (hi : ∀ x, q (cubic x) = q x) :
    nonzeroCount q = 0 ∨ nonzeroCount q = 6 ∨ nonzeroCount q = 12 := by
  rw [count_eq_profile q hi]
  have census : ∀ c : Fin 5 → ZMod 2,
      c 0 + c 1 + c 2 + c 3 + c 4 = 0 →
      profileCount c = 0 ∨ profileCount c = 6 ∨ profileCount c = 12 := by decide +kernel
  exact census _ (parity q hi)

theorem last_value_zero (q : QuadraticForm (ZMod 2) Space)
    (hi : ∀ x, q (cubic x) = q x) (h01 : q (rep 0) = q (rep 1))
    (h2 : q (rep 2) = 0) (h3 : q (rep 3) = 0) : q (rep 4) = 0 := by
  have h := parity q hi
  rw [h01, h2, h3] at h
  have hb : ∀ a b : ZMod 2, a + a + 0 + 0 + b = 0 → b = 0 := by decide +kernel
  exact hb _ _ h

def quaternionSquare (v : Space) : ZMod 2 :=
  (v.1.1 ^ 2 + v.1.1 * v.1.2 + v.1.2 ^ 2) +
  (v.2.1 ^ 2 + v.2.1 * v.2.2 + v.2.2 ^ 2)

theorem quaternionSquare_orbit : ∀ j k, quaternionSquare (orbit j k) =
    if j = 3 ∨ j = 4 then 1 else 0 := by decide +kernel

theorem zero_on_order_four (q : QuadraticForm (ZMod 2) Space)
    (hi : ∀ x, q (cubic x) = q x) (h01 : q (rep 0) = q (rep 1))
    (h2 : q (rep 2) = 0) (h3 : q (rep 3) = 0)
    (v : Space) (hv : quaternionSquare v = 1) : q v = 0 := by
  obtain ⟨o, rfl⟩ := orbitEquiv.surjective v
  rcases o with _ | ⟨j,k⟩
  · exact (show (0 : ZMod 2) ≠ 1 by decide) hv |>.elim
  · change quaternionSquare (orbit j k) = 1 at hv
    rw [quaternionSquare_orbit] at hv
    have hj : j = 3 ∨ j = 4 := by
      split_ifs at hv with hj
      · exact hj
      · exact (show (0 : ZMod 2) ≠ 1 by decide) hv |>.elim
    change q (orbit j k) = 0
    rw [orbit_invariant q hi]
    rcases hj with rfl | rfl
    · exact h3
    · exact last_value_zero q hi h01 h2 h3

/-- In particular neither of the two forbidden source counts can occur. -/
theorem count_ne_three_and_nine (q : QuadraticForm (ZMod 2) Space)
    (hi : ∀ x, q (cubic x) = q x) :
    nonzeroCount q ≠ 3 ∧ nonzeroCount q ≠ 9 := by
  rcases count_cases q hi with h | h | h <;> omega

/-- The zero branch of the source census really has zero square form. -/
theorem zero_of_marked_zero (q : QuadraticForm (ZMod 2) Space)
    (hi : ∀ x, q (cubic x) = q x) (h01 : q (rep 0) = q (rep 1))
    (h2 : q (rep 2) = 0) (h3 : q (rep 3) = 0) (h0 : q (rep 0) = 0) : q = 0 := by
  have h1 : q (rep 1) = 0 := h01.symm.trans h0
  have h4 := last_value_zero q hi h01 h2 h3
  ext v
  obtain ⟨o, rfl⟩ := orbitEquiv.surjective v
  rcases o with _ | ⟨j,k⟩
  · exact q.map_zero
  · change q (orbit j k) = 0
    rw [orbit_invariant q hi]
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4

/-- With the source fusion marks the two possibilities reduce to 0 and 6. -/
theorem count_of_marking (q : QuadraticForm (ZMod 2) Space)
    (hi : ∀ x, q (cubic x) = q x) (h01 : q (rep 0) = q (rep 1))
    (h2 : q (rep 2) = 0) (h3 : q (rep 3) = 0) :
    nonzeroCount q = if q (rep 0) = 0 then 0 else 6 := by
  rw [count_eq_profile q hi]
  have census : ∀ c : Fin 5 → ZMod 2,
      c 0 = c 1 → c 2 = 0 → c 3 = 0 → c 4 = 0 →
      profileCount c = if c 0 = 0 then 0 else 6 := by decide +kernel
  exact census _ h01 h2 h3 (last_value_zero q hi h01 h2 h3)

/-- The coordinates carry the literal order-three action. -/
theorem cubic_orbit : ∀ j k, cubic (orbit j k) = orbit j (k + 1) := by decide +kernel

theorem cubic_cube : ∀ v, cubic (cubic (cubic v)) = v := by decide +kernel

theorem cubic_fixed_iff : ∀ v, cubic v = v ↔ v = 0 := by decide +kernel

end Theory.LinearAlgebra.BinaryCubicOrbits
