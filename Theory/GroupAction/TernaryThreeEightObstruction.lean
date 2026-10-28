module

public import Theory.GroupAction.TernaryThreeEightModel
public import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

/-!
# The ternary order-eight swap obstruction

An involution swapping infinity with the identity and conjugating the standard
order-eight torus to its fifth power cannot belong to a group whose infinity
stabilizer consists of translations followed by powers of that torus.

The proof encodes the 28 points in orbit order: infinity, the identity, a
length-two orbit, and three length-eight orbits. Equivariance reconstructs a
swap from its values on four orbit representatives. Two kernel computations
(one for each short-orbit phase) check all possible images of the three long
representatives satisfying their involution equations. The word
`τ * translation z⁻¹ * τ * translation u * τ`, with `u = (0,0,1)` and
`τ (some u) = some z`, fails to be affine in every case. Its value at the
identity determines the only possible translation part, leaving eight linear
parts to exclude. This word belongs to the subgroup and fixes infinity.

All coordinate tables, their interpretation in the original action, and the
finite obstruction are proved by kernel reduction. The motivating source is
the abelian case of Suzuki (1965), Section III, Lemma 12; the finite calculation
is carried out here rather than assumed from an external enumeration.
-/

namespace TernaryThreeEight

private abbrev B := Fin 28

/-- Orbit order: infinity, identity, the short orbit, then the three long orbits. -/
private def point : B → Option V :=
  ![none, some (Multiplicative.ofAdd (0, 0, 0)),
    some (Multiplicative.ofAdd (1, 0, 0)),
    some (Multiplicative.ofAdd (2, 0, 0)),
    some (Multiplicative.ofAdd (0, 0, 1)),
    some (Multiplicative.ofAdd (0, 1, 1)),
    some (Multiplicative.ofAdd (0, 1, 2)),
    some (Multiplicative.ofAdd (0, 2, 0)),
    some (Multiplicative.ofAdd (0, 0, 2)),
    some (Multiplicative.ofAdd (0, 2, 2)),
    some (Multiplicative.ofAdd (0, 2, 1)),
    some (Multiplicative.ofAdd (0, 1, 0)),
    some (Multiplicative.ofAdd (1, 0, 1)),
    some (Multiplicative.ofAdd (2, 1, 1)),
    some (Multiplicative.ofAdd (1, 1, 2)),
    some (Multiplicative.ofAdd (2, 2, 0)),
    some (Multiplicative.ofAdd (1, 0, 2)),
    some (Multiplicative.ofAdd (2, 2, 2)),
    some (Multiplicative.ofAdd (1, 2, 1)),
    some (Multiplicative.ofAdd (2, 1, 0)),
    some (Multiplicative.ofAdd (1, 1, 0)),
    some (Multiplicative.ofAdd (2, 0, 1)),
    some (Multiplicative.ofAdd (1, 1, 1)),
    some (Multiplicative.ofAdd (2, 1, 2)),
    some (Multiplicative.ofAdd (1, 2, 0)),
    some (Multiplicative.ofAdd (2, 0, 2)),
    some (Multiplicative.ofAdd (1, 2, 2)),
    some (Multiplicative.ofAdd (2, 2, 1))]

private def unpoint : Option V → B
  | none => 0
  | some v =>
    (![1, 4, 8, 11, 5, 6, 7, 10, 9, 2, 12, 16, 20, 22, 14, 24, 18, 26, 3, 21, 25, 19, 13, 23,
      15, 27, 17]) (⟨v.toAdd.1.val * 9 + v.toAdd.2.1.val * 3 + v.toAdd.2.2.val, by
      have := v.toAdd.1.val_lt
      have := v.toAdd.2.1.val_lt
      have := v.toAdd.2.2.val_lt
      omega⟩ : Fin 27)

private theorem point_unpoint : ∀ p, point (unpoint p) = p := by decide +kernel

private theorem unpoint_point : ∀ b, unpoint (point b) = b := by decide +kernel

private theorem point_injective : Function.Injective point :=
  Function.LeftInverse.injective unpoint_point

private def rotate (n : ℕ) (b : B) : B :=
  if b.val < 2 then b else if b.val < 4 then ⟨2 + (b.val - 2 + n) % 2, by omega⟩
  else ⟨4 + (b.val - 4) / 8 * 8 + (b.val - 4 + n) % 8, by
    have := b.isLt
    omega⟩

private def phase (b : B) : Fin 8 :=
  ⟨if b.val < 4 then (b.val - 2) % 2 else (b.val - 4) % 8, by split_ifs <;> omega⟩

private def representative (b : B) : B :=
  if b.val < 4 then 2 else if b.val < 12 then 4 else if b.val < 20 then 12 else 20

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem point_rotate : ∀ (n : Fin 8) (b : B),
    point (rotate n.val b) = (linear ^ n.val) (point b) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem point_rotate_five : ∀ (n : Fin 8) (b : B),
    point (rotate (5 * n.val) b) = ((linear ^ 5) ^ n.val) (point b) := by decide +kernel

private theorem point_decomposition : ∀ b : B, b ≠ 0 → b ≠ 1 →
    point b = (linear ^ (phase b).val) (point (representative b)) := by decide +kernel

private def neg : B → B :=
  ![0, 1, 3, 2, 8, 9, 10, 11, 4, 5, 6, 7, 25, 26, 27, 20, 21, 22, 23, 24, 15, 16, 17, 18, 19, 12, 13, 14]

/-- The translation table, subsequently checked against the original action. -/
private def shift : B → B → B :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
  ![0, 2, 3, 1, 12, 22, 14, 24, 16, 26, 18, 20, 21, 5, 23, 7, 25, 9, 27, 11, 19, 4, 13, 6, 15, 8, 17, 10],
  ![0, 3, 1, 2, 21, 13, 23, 15, 25, 17, 27, 19, 4, 22, 6, 24, 8, 26, 10, 20, 11, 12, 5, 14, 7, 16, 9, 18],
  ![0, 4, 12, 21, 8, 6, 11, 10, 1, 7, 9, 5, 16, 23, 20, 27, 2, 15, 26, 13, 22, 25, 14, 19, 18, 3, 24, 17],
  ![0, 5, 22, 13, 6, 9, 7, 4, 11, 1, 8, 10, 14, 17, 24, 21, 20, 3, 16, 27, 18, 23, 26, 15, 12, 19, 2, 25],
  ![0, 6, 14, 23, 11, 7, 10, 8, 5, 4, 1, 9, 20, 15, 18, 25, 22, 21, 2, 17, 26, 19, 24, 27, 16, 13, 12, 3],
  ![0, 7, 24, 15, 10, 4, 8, 11, 9, 6, 5, 1, 18, 21, 16, 19, 26, 23, 22, 3, 2, 27, 12, 25, 20, 17, 14, 13],
  ![0, 8, 16, 25, 1, 11, 5, 9, 4, 10, 7, 6, 2, 19, 22, 17, 12, 27, 24, 23, 14, 3, 20, 13, 26, 21, 18, 15],
  ![0, 9, 26, 17, 7, 1, 4, 6, 10, 5, 11, 8, 24, 3, 12, 23, 18, 13, 20, 25, 16, 15, 2, 21, 14, 27, 22, 19],
  ![0, 10, 18, 27, 9, 8, 1, 5, 7, 11, 6, 4, 26, 25, 2, 13, 24, 19, 14, 21, 12, 17, 16, 3, 22, 15, 20, 23],
  ![0, 11, 20, 19, 5, 10, 9, 1, 6, 8, 4, 7, 22, 27, 26, 3, 14, 25, 12, 15, 24, 13, 18, 17, 2, 23, 16, 21],
  ![0, 12, 21, 4, 16, 14, 20, 18, 2, 24, 26, 22, 25, 6, 19, 10, 3, 7, 17, 5, 13, 8, 23, 11, 27, 1, 15, 9],
  ![0, 13, 5, 22, 23, 17, 15, 21, 19, 3, 25, 27, 6, 26, 7, 12, 11, 2, 8, 18, 10, 14, 9, 24, 4, 20, 1, 16],
  ![0, 14, 23, 6, 20, 24, 18, 16, 22, 12, 2, 26, 19, 7, 27, 8, 13, 4, 3, 9, 17, 11, 15, 10, 25, 5, 21, 1],
  ![0, 15, 7, 24, 27, 21, 25, 19, 17, 23, 13, 3, 10, 12, 8, 20, 9, 14, 5, 2, 1, 18, 4, 16, 11, 26, 6, 22],
  ![0, 16, 25, 8, 2, 20, 22, 26, 12, 18, 24, 14, 3, 11, 13, 9, 21, 10, 15, 6, 23, 1, 19, 5, 17, 4, 27, 7],
  ![0, 17, 9, 26, 15, 3, 21, 23, 27, 13, 19, 25, 7, 2, 4, 14, 10, 22, 11, 16, 8, 24, 1, 12, 6, 18, 5, 20],
  ![0, 18, 27, 10, 26, 16, 2, 22, 24, 20, 14, 12, 17, 8, 3, 5, 15, 11, 23, 4, 21, 9, 25, 1, 13, 7, 19, 6],
  ![0, 19, 11, 20, 13, 27, 17, 3, 23, 25, 21, 15, 5, 18, 9, 2, 6, 16, 4, 24, 7, 22, 10, 26, 1, 14, 8, 12],
  ![0, 20, 19, 11, 22, 18, 26, 2, 14, 16, 12, 24, 13, 10, 17, 1, 23, 8, 21, 7, 15, 5, 27, 9, 3, 6, 25, 4],
  ![0, 21, 4, 12, 25, 23, 19, 27, 3, 15, 17, 13, 8, 14, 11, 18, 1, 24, 9, 22, 5, 16, 6, 20, 10, 2, 7, 26],
  ![0, 22, 13, 5, 14, 26, 24, 12, 20, 2, 16, 18, 23, 9, 15, 4, 19, 1, 25, 10, 27, 6, 17, 7, 21, 11, 3, 8],
  ![0, 23, 6, 14, 19, 15, 27, 25, 13, 21, 3, 17, 11, 24, 10, 16, 5, 12, 1, 26, 9, 20, 7, 18, 8, 22, 4, 2],
  ![0, 24, 15, 7, 18, 12, 16, 20, 26, 14, 22, 2, 27, 4, 25, 11, 17, 6, 13, 1, 3, 10, 21, 8, 19, 9, 23, 5],
  ![0, 25, 8, 16, 3, 19, 13, 17, 21, 27, 15, 23, 1, 20, 5, 26, 4, 18, 7, 14, 6, 2, 11, 22, 9, 12, 10, 24],
  ![0, 26, 17, 9, 24, 2, 12, 14, 18, 22, 20, 16, 15, 1, 21, 6, 27, 5, 19, 8, 25, 7, 3, 4, 23, 10, 13, 11],
  ![0, 27, 10, 18, 17, 25, 3, 13, 15, 19, 23, 21, 9, 16, 1, 22, 7, 20, 6, 12, 4, 26, 8, 2, 5, 24, 11, 14]]

private def value (b : B) : V := (point b).getD 1

private theorem point_shift : ∀ a b : B,
    point (shift a b) = translation (value a) (point b) := by decide +kernel

private theorem value_neg : ∀ b : B, value (neg b) = (value b)⁻¹ := by decide +kernel

private abbrev Code := Fin 2 × B × B × B

private def applyCode (c : Code) (b : B) : B :=
  if b = 0 then 1 else if b = 1 then 0 else
  rotate (5 * (phase b).val)
    (if b.val < 4 then ⟨2 + c.1.val, by omega⟩ else
     if b.val < 12 then c.2.1 else if b.val < 20 then c.2.2.1 else c.2.2.2)

private def word (c : Code) (b : B) : B :=
  applyCode c (shift (neg (applyCode c 4))
    (applyCode c (shift 4 (applyCode c b))))
/-- Only the involution equations on the three long representatives are needed. -/
private def good (c : Code) : Prop :=
  applyCode c (applyCode c 4) = 4 ∧
  applyCode c (applyCode c 12) = 12 ∧
  applyCode c (applyCode c 20) = 20
private instance (c : Code) : Decidable (good c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))


private theorem involutive_of_square (τ : Equiv.Perm (Option V)) (hsq : τ ^ 2 = 1) :
    Function.Involutive τ := by
  intro p
  have h := congrArg (fun s : Equiv.Perm (Option V) => s p) hsq
  simpa [pow_two, Equiv.Perm.mul_apply] using h

private theorem twist (τ : Equiv.Perm (Option V)) (hsq : τ ^ 2 = 1)
    (hc : τ⁻¹ * linear * τ = linear ^ 5) : SemiconjBy τ linear (linear ^ 5) := by
  have hh : τ * τ = 1 := by simpa [pow_two] using hsq
  have hi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hh
  change τ * linear = linear ^ 5 * τ
  calc
    τ * linear = (τ⁻¹ * linear * τ) * τ := by rw [hi, mul_assoc (τ * linear), hh, mul_one]
    _ = linear ^ 5 * τ := by rw [hc]

private theorem twist_apply (τ : Equiv.Perm (Option V)) (hsq : τ ^ 2 = 1)
    (hc : τ⁻¹ * linear * τ = linear ^ 5) (n : ℕ) (p : Option V) :
    τ ((linear ^ n) p) = ((linear ^ 5) ^ n) (τ p) := by
  exact congrArg (fun s : Equiv.Perm (Option V) => s p) ((twist τ hsq hc).pow_right n)

private theorem short_test : ∀ b : B,
    point b ≠ none → point b ≠ some 1 →
    ((linear ^ 5) ^ (2 : ℕ)) (point b) = point b →
    ∃ a : Fin 2, b = ⟨2 + a.val, by omega⟩ := by decide +kernel

private theorem short_image (τ : Equiv.Perm (Option V)) (hsq : τ ^ 2 = 1)
    (hn : τ none = some 1) (hc : τ⁻¹ * linear * τ = linear ^ 5) :
    ∃ a : Fin 2, unpoint (τ (point 2)) = ⟨2 + a.val, by omega⟩ := by
  have hi := involutive_of_square τ hsq
  have hz : τ (some 1) = none := by rw [← hn, hi]
  apply short_test
  · rw [point_unpoint]
    intro heq
    have h := τ.injective (heq.trans hz.symm)
    exact (by decide : point 2 ≠ some 1) h
  · rw [point_unpoint]
    intro heq
    have h := τ.injective (heq.trans hn.symm)
    exact (by decide : point 2 ≠ none) h
  · rw [point_unpoint, ← twist_apply τ hsq hc]
    congr 1

private def code (τ : Equiv.Perm (Option V)) (a : Fin 2) : Code :=
  (a, unpoint (τ (point 4)), unpoint (τ (point 12)), unpoint (τ (point 20)))

private theorem apply_code (τ : Equiv.Perm (Option V)) (hsq : τ ^ 2 = 1)
    (hn : τ none = some 1) (hc : τ⁻¹ * linear * τ = linear ^ 5)
    (a : Fin 2) (ha : unpoint (τ (point 2)) = ⟨2 + a.val, by omega⟩) (b : B) :
    point (applyCode (code τ a) b) = τ (point b) := by
  have hz : τ (some 1) = none := by
    rw [← hn, involutive_of_square τ hsq]
  by_cases h0 : b = 0
  · subst b
    exact hn.symm
  by_cases h1 : b = 1
  · subst b
    exact hz.symm
  rw [applyCode, if_neg h0, if_neg h1, point_rotate_five]
  rw [point_decomposition b h0 h1, twist_apply τ hsq hc]
  congr 1
  simp only [code, representative]
  split_ifs with h2 h3 h4
  · rw [← ha, point_unpoint]
  · exact point_unpoint _
  · exact point_unpoint _
  · exact point_unpoint _
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem certificate_zero : ∀ b c d : B, good (0,b,c,d) →
    ∀ n : Fin 8, ∃ x : B,
      word (0,b,c,d) x ≠ shift (word (0,b,c,d) 1) (rotate n.val x) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem certificate_one : ∀ b c d : B, good (1,b,c,d) →
    ∀ n : Fin 8, ∃ x : B,
      word (1,b,c,d) x ≠ shift (word (1,b,c,d) 1) (rotate n.val x) := by
  decide +kernel


private theorem certificate (c : Code) (hg : good c) (n : Fin 8) :
    ∃ x : B, word c x ≠ shift (word c 1) (rotate n.val x) := by
  rcases c with ⟨a, b, c, d⟩
  fin_cases a
  · exact certificate_zero b c d hg n
  · exact certificate_one b c d hg n

private theorem good_code (τ : Equiv.Perm (Option V)) (hsq : τ ^ 2 = 1)
    (hn : τ none = some 1) (hc : τ⁻¹ * linear * τ = linear ^ 5)
    (a : Fin 2) (ha : unpoint (τ (point 2)) = ⟨2 + a.val, by omega⟩) :
    good (code τ a) := by
  have hi (b : B) : applyCode (code τ a) (applyCode (code τ a) b) = b := by
    apply point_injective
    rw [apply_code τ hsq hn hc a ha, apply_code τ hsq hn hc a ha,
      involutive_of_square τ hsq]
  exact ⟨hi 4, hi 12, hi 20⟩

private theorem point_word (τ : Equiv.Perm (Option V)) (hsq : τ ^ 2 = 1)
    (hn : τ none = some 1) (hc : τ⁻¹ * linear * τ = linear ^ 5)
    (a : Fin 2) (ha : unpoint (τ (point 2)) = ⟨2 + a.val, by omega⟩)
    (z : V) (hz : τ (some (Multiplicative.ofAdd (0, 0, 1))) = some z) (b : B) :
    point (word (code τ a) b) =
      (τ * translation z⁻¹ * τ * translation (Multiplicative.ofAdd (0, 0, 1)) * τ)
        (point b) := by
  have hv : value (applyCode (code τ a) 4) = z := by
    unfold value
    rw [apply_code τ hsq hn hc a ha]
    change (τ (some (Multiplicative.ofAdd (0, 0, 1)))).getD 1 = z
    rw [hz]
    rfl
  rw [word, apply_code τ hsq hn hc a ha, point_shift, value_neg, hv,
    apply_code τ hsq hn hc a ha, point_shift, apply_code τ hsq hn hc a ha]
  rfl

private theorem linear_one : ∀ n : Fin 8, (linear ^ n.val) (some 1) = some 1 := by
  decide +kernel

/-- The stabilizing word associated with the vector `(0,0,1)` cannot be affine. -/
public theorem swap_word_ne_affine (τ : Equiv.Perm (Option V)) (hsq : τ ^ 2 = 1)
    (hn : τ none = some 1) (hc : τ⁻¹ * linear * τ = linear ^ 5)
    (z : V) (hz : τ (some (Multiplicative.ofAdd (0, 0, 1))) = some z)
    (v : V) (n : Fin 8) :
    τ * translation z⁻¹ * τ * translation (Multiplicative.ofAdd (0, 0, 1)) * τ ≠
      translation v * linear ^ n.val := by
  obtain ⟨a, ha⟩ := short_image τ hsq hn hc
  obtain ⟨x, hx⟩ := certificate (code τ a) (good_code τ hsq hn hc a ha) n
  intro heq
  have hv : value (word (code τ a) 1) = v := by
    unfold value
    rw [point_word τ hsq hn hc a ha z hz, heq]
    change ((translation v * linear ^ n.val) (some 1)).getD 1 = v
    rw [Equiv.Perm.mul_apply, linear_one n]
    change (some (v * 1)).getD 1 = v
    simp
  apply hx
  apply point_injective
  rw [point_word τ hsq hn hc a ha z hz, heq, point_shift, hv, point_rotate n]
  rfl

/-- A subgroup containing the translations with the indicated affine infinity
stabilizer contains no involution swapping infinity and one and twisting the
standard order-eight torus by the fifth power. -/
public theorem swap_obstruction (L : Subgroup (Equiv.Perm (Option V)))
    (htrans : ∀ v : V, translation v ∈ L)
    (haff : ∀ s : Equiv.Perm (Option V), s ∈ L → s none = none →
      ∃ (v : V) (n : Fin 8), s = translation v * linear ^ n.val)
    (τ : Equiv.Perm (Option V)) (hτ : τ ∈ L) (hsq : τ ^ 2 = 1)
    (hn : τ none = some 1) (hc : τ⁻¹ * linear * τ = linear ^ 5) : False := by
  have hi := involutive_of_square τ hsq
  have hz0 : τ (some 1) = none := by rw [← hn, hi]
  have hu : τ (some (Multiplicative.ofAdd (0, 0, 1))) ≠ none := by
    intro h
    have h' := τ.injective (h.trans hz0.symm)
    exact (by decide : (some (Multiplicative.ofAdd (0, 0, 1)) : Option V) ≠ some 1) h'
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp hu
  let W := τ * translation z⁻¹ * τ * translation (Multiplicative.ofAdd (0, 0, 1)) * τ
  have hW : W ∈ L := L.mul_mem (L.mul_mem (L.mul_mem (L.mul_mem hτ (htrans _)) hτ)
    (htrans _)) hτ
  have hfix : W none = none := by
    change τ (translation z⁻¹ (τ (translation (Multiplicative.ofAdd (0, 0, 1))
      (τ none)))) = none
    rw [hn]
    change τ (translation z⁻¹ (τ (some (Multiplicative.ofAdd (0, 0, 1) * 1)))) = none
    rw [mul_one, hz]
    change τ (some (z⁻¹ * z)) = none
    rw [inv_mul_cancel, hz0]
  obtain ⟨v, n, heq⟩ := haff W hW hfix
  exact swap_word_ne_affine τ hsq hn hc z hz v n heq
end TernaryThreeEight
