module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.Contracts
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
/-!
# Normalizing binary defects in the Held relators

Changing the generator lifts by a common central involution changes the seven
relator defects by the parity vector `(0, η, ε + η, 0, 0, 0, η)`. Thus the
seventh- and seventeenth-power relations can always be made exact.

The long commutator relation is already exact: a cyclic rotation expresses its
defect as a central commutation defect for `y`. Raising to the seventh power
kills that defect, since `y^7` is central and the defect has order dividing two.
These calculations give `Normalized`; its four remaining defects are not
asserted to vanish here. Neither finiteness nor perfectness is needed for this
normalization.

Source of the literal words and commutator convention: John Bray's ATLAS
`HeG1-P1`, retained in `Held/Model/Source/HeG1-P1.M`. No claim about the
presentation's faithfulness or the Held multiplier is used.
-/

namespace Held.CentralCovers.TwoPrimary.BinaryRelators
variable {E : Type*} [Group E]
private def centralMul : E × Subgroup.center E →* E where
  toFun p := p.1 * p.2
  map_one' := mul_one _
  map_mul' p q := by
    dsimp
    have h := Subgroup.mem_center_iff.mp p.2.property q.1
    calc
      p.1 * q.1 * ((p.2 : E) * q.2) = p.1 * (q.1 * p.2) * q.2 := by group
      _ = p.1 * (p.2 * q.1) * q.2 := by rw [h]
      _ = p.1 * p.2 * (q.1 * q.2) := by group

private theorem relationWord_twist (x y : E) (c d : Subgroup.center E) (i : Fin 7) :
    relationWord (x * c) (y * d) i =
      relationWord x y i * ((relationWord c d i : Subgroup.center E) : E) := by
  have h := map_relationWord (centralMul (E := E)) (x, c) (y, d) i
  have hfst := map_relationWord (MonoidHom.fst E (Subgroup.center E)) (x, c) (y, d) i
  have hsnd := map_relationWord (MonoidHom.snd E (Subgroup.center E)) (x, c) (y, d) i
  change (relationWord (x, c) (y, d) i).1 = relationWord x y i at hfst
  change (relationWord (x, c) (y, d) i).2 = relationWord c d i at hsnd
  change (relationWord (x, c) (y, d) i).1 *
    ((relationWord (x, c) (y, d) i).2 : E) = _ at h
  rw [hfst, hsnd] at h
  exact h.symm

private theorem word_of_one (z : E) (hs : z ^ 2 = 1) (ε η : Fin 2) (i : Fin 7) :
    relationWord (z ^ ε.val) (z ^ η.val) i =
      z ^ (match i with | 0 => 0 | 1 => η.val | 2 => ε.val + η.val
                        | 3 => 0 | 4 => 0 | 5 => 0 | 6 => η.val) := by
  have hz4 : z ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hs, one_pow]
  have hz7 : z ^ 7 = z := by
    calc
      z ^ 7 = (z ^ 2) ^ 3 * z := by group
      _ = z := by rw [hs]; simp
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs)
  fin_cases ε <;> fin_cases η <;> fin_cases i <;>
    simp only [pow_zero, pow_one, relationWord,
      one_mul, mul_one, one_pow, inv_one, hzi, ← pow_two, hs, Nat.reduceAdd]
  all_goals group <;> simp_all
  · exact (pow_eq_pow_of_modEq (a := 17) (b := 1) (by decide) hs).trans (pow_one z)
  · exact (pow_eq_pow_of_modEq (a := 17) (b := 1) (by decide) hs).trans (pow_one z)
  · exact (pow_eq_pow_of_modEq (a := 12) (b := 0) (by decide) hs).trans (pow_zero z)
  · exact (pow_eq_pow_of_modEq (a := 10) (b := 0) (by decide) hs).trans (pow_zero z)
  · exact (pow_eq_pow_of_modEq (a := 9) (b := 1) (by decide) hs).trans (pow_one z)

/-- The exact parity effect of changing both generator lifts. -/
public theorem relationWord_twist_binary (z x y : E)
    (hz : z ∈ Subgroup.center E) (hs : z ^ 2 = 1) (ε η : Fin 2) (i : Fin 7) :
    relationWord (x * z ^ ε.val) (y * z ^ η.val) i =
      relationWord x y i *
        z ^ (match i with | 0 => 0 | 1 => η.val | 2 => ε.val + η.val
                          | 3 => 0 | 4 => 0 | 5 => 0 | 6 => η.val) := by
  let c : Subgroup.center E := ⟨z, hz⟩
  have hcs : c ^ 2 = 1 := Subtype.ext hs
  have h := relationWord_twist x y (c ^ ε.val) (c ^ η.val) i
  rw [word_of_one c hcs ε η i] at h
  exact h

private theorem commutator_rotation (z x y : E) (hz : z ∈ Subgroup.center E) (hs : z ^ 2 = 1)
    (hx : x ^ 2 = z) :
    (y*x*y) * relationWord x y 3 * (y*x*y)⁻¹ =
      let u := x*y*x*y⁻¹*x*y⁻¹*x*y*x
      y*u*(u*y)⁻¹ := by
  have hxx : x * x = z := by simpa only [pow_two] using hx
  have hzz : z * z = 1 := by simpa only [pow_two] using hs
  have hzmove (g : E) : z * g = g * z := (Subgroup.mem_center_iff.mp hz g).symm
  have hxi : x⁻¹ = x * z := inv_eq_of_mul_eq_one_right (by
    calc
      x * (x * z) = (x * x) * z := (mul_assoc _ _ _).symm
      _ = 1 := by rw [hxx, hzz])
  dsimp only [relationWord]
  simp only [mul_inv_rev, hxi, mul_assoc, hzmove, hzz, mul_one]
  group
  simp only [zpow_neg_one, mul_assoc, hxx, hzmove, mul_inv_cancel_left]

private theorem defect_eq_one (z y u : E) (hz : z ∈ Subgroup.center E)
    (hs : z ^ 2 = 1) (hy : y ^ 7 ∈ Subgroup.center E)
    (hd : y * u * (u * y)⁻¹ = z) : z = 1 := by
  have hzmove (g : E) : z * g = g * z := (Subgroup.mem_center_iff.mp hz g).symm
  have hmul : y * u = z * (u * y) := (mul_inv_eq_iff_eq_mul).mp hd
  have hc : u⁻¹ * y * u = y * z := by
    calc
      u⁻¹ * y * u = u⁻¹ * (y * u) := mul_assoc _ _ _
      _ = u⁻¹ * (z * (u * y)) := by rw [hmul]
      _ = y * z := by simp only [hzmove, mul_assoc, inv_mul_cancel_left]
  have hp : u⁻¹ * y ^ 7 * u = (y * z) ^ 7 := by
    calc
      u⁻¹ * y ^ 7 * u = (u⁻¹ * y * u) ^ 7 := by
        simpa only [inv_inv] using (conj_pow (a := u⁻¹) (b := y) (i := 7)).symm
      _ = (y * z) ^ 7 := congrArg (fun t : E => t ^ 7) hc
  have h7 : z ^ 7 = z :=
    (pow_eq_pow_of_modEq (a := 7) (b := 1) (by decide) hs).trans (pow_one z)
  rw [(show Commute y z from Subgroup.mem_center_iff.mp hz y).mul_pow, h7,
    Subgroup.mem_center_iff.mp hy u⁻¹, mul_assoc, inv_mul_cancel, mul_one] at hp
  exact (mul_left_cancel (show y ^ 7 * z = y ^ 7 * 1 by simpa only [mul_one] using hp.symm))

/-- The fourth sourced relator has no binary central defect. Its cyclic
rotation is a commutation defect for an element with central seventh power. -/
public theorem long_commutator_eq_one (z x y : E) (hz : z ∈ Subgroup.center E)
    (hs : z ^ 2 = 1) (hx : x ^ 2 = 1 ∨ x ^ 2 = z)
    (hy : y ^ 7 = 1 ∨ y ^ 7 = z)
    (hr : relationWord x y 3 = 1 ∨ relationWord x y 3 = z) :
    relationWord x y 3 = 1 := by
  rcases hr with hr | hr
  · exact hr
  suffices hz1 : z = 1 by exact hr.trans hz1
  let u := x*y*x*y⁻¹*x*y⁻¹*x*y*x
  have hrot : (y*x*y) * relationWord x y 3 * (y*x*y)⁻¹ =
      y*u*(u*y)⁻¹ := by
    rcases hx with hx | hx
    · exact commutator_rotation 1 x y (Subgroup.one_mem _) (one_pow 2) hx
    · exact commutator_rotation z x y hz hs hx
  have hd : y*u*(u*y)⁻¹ = z := by
    rw [← hrot, hr, Subgroup.mem_center_iff.mp hz (y*x*y), mul_assoc,
      mul_inv_cancel, mul_one]
  apply defect_eq_one z y u hz hs _ hd
  rcases hy with hy | hy
  · rw [hy]; exact Subgroup.one_mem _
  · rw [hy]; exact hz

private theorem binary_mul {z a b : E} (hs : z ^ 2 = 1)
    (ha : a = 1 ∨ a = z) (hb : b = 1 ∨ b = z) : a * b = 1 ∨ a * b = z := by
  have hzz : z * z = 1 := by simpa only [pow_two] using hs
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hzz]

private theorem binary_pow (z : E) (hs : z ^ 2 = 1) (n : ℕ) :
    z ^ n = 1 ∨ z ^ n = z := by
  induction n with
  | zero => exact Or.inl (pow_zero _)
  | succ n ih =>
    rw [pow_succ]
    exact binary_mul hs ih (Or.inr rfl)

private theorem binary_twist (z x y : E) (hz : z ∈ Subgroup.center E)
    (hs : z ^ 2 = 1) (hr : ∀ i : Fin 7, relationWord x y i = 1 ∨ relationWord x y i = z)
    (ε η : Fin 2) (i : Fin 7) :
    relationWord (x * z ^ ε.val) (y * z ^ η.val) i = 1 ∨
      relationWord (x * z ^ ε.val) (y * z ^ η.val) i = z := by
  rw [relationWord_twist_binary z x y hz hs]
  exact binary_mul hs (hr i) (binary_pow z hs _)

private theorem odd_relators_normalize (z x y : E) (hz : z ∈ Subgroup.center E)
    (hs : z ^ 2 = 1)
    (h1 : relationWord x y 1 = 1 ∨ relationWord x y 1 = z)
    (h2 : relationWord x y 2 = 1 ∨ relationWord x y 2 = z) :
    ∃ ε η : Fin 2,
      relationWord (x * z ^ ε.val) (y * z ^ η.val) 1 = 1 ∧
      relationWord (x * z ^ ε.val) (y * z ^ η.val) 2 = 1 := by
  have hzz : z * z = 1 := by simpa only [pow_two] using hs
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · refine ⟨0, 0, ?_, ?_⟩ <;>
      rw [relationWord_twist_binary z x y hz hs] <;> simp [h1, h2]
  · refine ⟨1, 0, ?_, ?_⟩ <;>
      rw [relationWord_twist_binary z x y hz hs] <;> simp [h1, h2, hzz]
  · refine ⟨1, 1, ?_, ?_⟩ <;>
      rw [relationWord_twist_binary z x y hz hs] <;> simp [h1, h2, hzz, hs]
  · refine ⟨0, 1, ?_, ?_⟩ <;>
      rw [relationWord_twist_binary z x y hz hs] <;> simp [h1, h2, hzz]

/-- The normalized input retains all seven sourced words and no conclusion
about their four remaining defects. The odd-order and long-commutator clauses
are established by `normalize`, not assumed of the original lifts. -/
public structure Normalized (z x y : E) : Prop where
  central : z ∈ Subgroup.center E
  square : z ^ 2 = 1
  defects : ∀ i : Fin 7, relationWord x y i = 1 ∨ relationWord x y i = z
  seventh : y ^ 7 = 1
  seventeenth : (x * y) ^ 17 = 1
  long_commutator : relationWord x y 3 = 1

/-- Remove the two odd-power defects and prove the long commutator relation,
while retaining the original binary alternatives for every relator. -/
public theorem normalize (z x y : E) (hz : z ∈ Subgroup.center E) (hs : z ^ 2 = 1)
    (hr : ∀ i : Fin 7, relationWord x y i = 1 ∨ relationWord x y i = z) :
    ∃ ε η : Fin 2, Normalized z (x * z ^ ε.val) (y * z ^ η.val) := by
  obtain ⟨ε, η, h1, h2⟩ := odd_relators_normalize z x y hz hs (hr 1) (hr 2)
  have hd := binary_twist z x y hz hs hr ε η
  refine ⟨ε, η, hz, hs, hd, h1, h2, ?_⟩
  exact long_commutator_eq_one z _ _ hz hs (hd 0) (hd 1) (hd 3)

/-- With the common involution equal to one there are no defects. -/
public theorem lift_of_trivial_involution (x y : E)
    (hr : ∀ i : Fin 7, relationWord x y i = 1 ∨ relationWord x y i = (1 : E)) :
    ∃ ε η : Fin 2, ∀ i : Fin 7,
      relationWord (x * (1 : E) ^ ε.val) (y * (1 : E) ^ η.val) i = 1 := by
  refine ⟨0, 0, ?_⟩
  intro i
  simpa only [one_pow, mul_one, or_self] using hr i
end Held.CentralCovers.TwoPrimary.BinaryRelators
