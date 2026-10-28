module

public import Theory.SpecificGroups.UnitaryThree.RootTorus
public import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

/-!
# Rigidity of the Hermitian swapping permutation

The scalar torus has one orbit of length two and three of length eight away
from infinity and the identity. A swapping involution which intertwines the
torus by its fifth power is determined by four representative images.
The word `τ * rootPerm z⁻¹ * τ * rootPerm u * τ`, where `τ u = z`, fixes
infinity. Requiring it to be affine leaves exactly the reciprocal permutation
and its product with the fourth power of the torus generator.

The coordinate tables and the exhaustive finite certificate are checked by
kernel reduction. The proof follows the same orbit method as the ternary
abelian obstruction, now for the nonabelian Hermitian root group.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Sections V–VI, specialized here to q = 3 by a finite calculation.
-/

namespace UnitaryThree.SwapRigidity

/-- The scalar `1 + i`, generating the eight nonzero elements of F₉. -/
@[expose] public def scalar : FiniteField.Nineˣ :=
  ⟨⟨1, 1⟩, ⟨2, 1⟩, by decide, by decide⟩

/-- Every scalar is one of the eight powers of `1 + i`. -/
public theorem scalar_powers : ∀ r : FiniteField.Nineˣ,
    ∃ n : Fin 8, r = scalar ^ n.val := by decide +kernel

private def linear : Equiv.Perm Point := torusPerm scalar
private def u : Root := ⟨(⟨0, 1⟩, ⟨1, 0⟩), by decide⟩

private abbrev B := Fin 28

/-- Orbit order: infinity, identity, the short orbit, then the three long orbits. -/
private def point : B → Point :=
  ![none,
    some ⟨(⟨0, 0⟩, ⟨0, 0⟩), by decide⟩,
    some ⟨(⟨0, 0⟩, ⟨0, 1⟩), by decide⟩,
    some ⟨(⟨0, 0⟩, ⟨0, 2⟩), by decide⟩,
    some ⟨(⟨0, 1⟩, ⟨1, 0⟩), by decide⟩,
    some ⟨(⟨2, 1⟩, ⟨2, 0⟩), by decide⟩,
    some ⟨(⟨1, 0⟩, ⟨1, 0⟩), by decide⟩,
    some ⟨(⟨1, 1⟩, ⟨2, 0⟩), by decide⟩,
    some ⟨(⟨0, 2⟩, ⟨1, 0⟩), by decide⟩,
    some ⟨(⟨1, 2⟩, ⟨2, 0⟩), by decide⟩,
    some ⟨(⟨2, 0⟩, ⟨1, 0⟩), by decide⟩,
    some ⟨(⟨2, 2⟩, ⟨2, 0⟩), by decide⟩,
    some ⟨(⟨0, 1⟩, ⟨1, 1⟩), by decide⟩,
    some ⟨(⟨2, 1⟩, ⟨2, 2⟩), by decide⟩,
    some ⟨(⟨1, 0⟩, ⟨1, 1⟩), by decide⟩,
    some ⟨(⟨1, 1⟩, ⟨2, 2⟩), by decide⟩,
    some ⟨(⟨0, 2⟩, ⟨1, 1⟩), by decide⟩,
    some ⟨(⟨1, 2⟩, ⟨2, 2⟩), by decide⟩,
    some ⟨(⟨2, 0⟩, ⟨1, 1⟩), by decide⟩,
    some ⟨(⟨2, 2⟩, ⟨2, 2⟩), by decide⟩,
    some ⟨(⟨0, 1⟩, ⟨1, 2⟩), by decide⟩,
    some ⟨(⟨2, 1⟩, ⟨2, 1⟩), by decide⟩,
    some ⟨(⟨1, 0⟩, ⟨1, 2⟩), by decide⟩,
    some ⟨(⟨1, 1⟩, ⟨2, 1⟩), by decide⟩,
    some ⟨(⟨0, 2⟩, ⟨1, 2⟩), by decide⟩,
    some ⟨(⟨1, 2⟩, ⟨2, 1⟩), by decide⟩,
    some ⟨(⟨2, 0⟩, ⟨1, 2⟩), by decide⟩,
    some ⟨(⟨2, 2⟩, ⟨2, 1⟩), by decide⟩]

private def unpoint : Point → B
  | none => 0
  | some p =>
    (![1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 12, 20, 1, 1, 1, 1, 1, 1, 8, 16, 24, 1, 1, 1, 1, 1, 1, 6, 14, 22, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 23, 15, 1, 1, 1, 1, 1, 1, 9, 25, 17, 1, 1, 1, 10, 18, 26, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 21, 13, 1, 1, 1, 1, 1, 1, 11, 27, 19]) (⟨p.val.1.re.val * 27 + p.val.1.im.val * 9 +
      p.val.2.re.val * 3 + p.val.2.im.val, by
      have := p.val.1.re.val_lt
      have := p.val.1.im.val_lt
      have := p.val.2.re.val_lt
      have := p.val.2.im.val_lt
      omega⟩ : Fin 81)

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
  ![0, 1, 3, 2, 8, 9, 10, 11, 4, 5, 6, 7, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19, 12, 13, 14, 15]

/-- Multiplication by a root, with the first row representing the identity. -/
private def shift : B → B → B :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
    ![0, 2, 3, 1, 12, 21, 14, 23, 16, 25, 18, 27, 20, 5, 22, 7, 24, 9, 26, 11, 4, 13, 6, 15, 8, 17, 10, 19],
    ![0, 3, 1, 2, 20, 13, 22, 15, 24, 17, 26, 19, 4, 21, 6, 23, 8, 25, 10, 27, 12, 5, 14, 7, 16, 9, 18, 11],
    ![0, 4, 12, 20, 8, 19, 23, 25, 1, 14, 13, 26, 16, 27, 15, 9, 2, 6, 5, 18, 24, 11, 7, 17, 3, 22, 21, 10],
    ![0, 5, 21, 13, 27, 9, 12, 24, 26, 1, 15, 14, 19, 17, 20, 16, 10, 3, 7, 6, 11, 25, 4, 8, 18, 2, 23, 22],
    ![0, 6, 14, 22, 15, 20, 10, 13, 25, 27, 1, 16, 7, 12, 18, 21, 17, 11, 2, 8, 23, 4, 26, 5, 9, 19, 3, 24],
    ![0, 7, 23, 15, 17, 16, 21, 11, 14, 26, 20, 1, 9, 8, 13, 19, 22, 18, 4, 3, 25, 24, 5, 27, 6, 10, 12, 2],
    ![0, 8, 16, 24, 1, 18, 17, 22, 4, 15, 27, 21, 2, 10, 9, 14, 12, 23, 19, 5, 3, 26, 25, 6, 20, 7, 11, 13],
    ![0, 9, 25, 17, 22, 1, 19, 18, 23, 5, 16, 20, 6, 3, 11, 10, 15, 13, 24, 12, 14, 2, 27, 26, 7, 21, 8, 4],
    ![0, 10, 18, 26, 21, 23, 1, 12, 19, 24, 6, 17, 13, 7, 2, 4, 11, 16, 14, 25, 5, 15, 3, 20, 27, 8, 22, 9],
    ![0, 11, 27, 19, 18, 22, 24, 1, 13, 12, 25, 7, 26, 14, 8, 3, 5, 4, 17, 15, 10, 6, 16, 2, 21, 20, 9, 23],
    ![0, 12, 20, 4, 16, 11, 15, 17, 2, 22, 5, 10, 24, 19, 7, 25, 3, 14, 21, 26, 8, 27, 23, 9, 1, 6, 13, 18],
    ![0, 13, 5, 21, 11, 17, 4, 16, 18, 3, 23, 6, 27, 25, 12, 8, 26, 2, 15, 22, 19, 9, 20, 24, 10, 1, 7, 14],
    ![0, 14, 22, 6, 7, 4, 18, 5, 17, 19, 2, 24, 23, 20, 26, 13, 9, 27, 3, 16, 15, 12, 10, 21, 25, 11, 1, 8],
    ![0, 15, 7, 23, 25, 8, 5, 19, 6, 18, 12, 3, 17, 24, 21, 27, 14, 10, 20, 2, 9, 16, 13, 11, 22, 26, 4, 1],
    ![0, 16, 24, 8, 2, 26, 9, 6, 12, 7, 19, 13, 3, 18, 25, 22, 20, 15, 11, 21, 1, 10, 17, 14, 4, 23, 27, 5],
    ![0, 17, 9, 25, 14, 3, 27, 10, 7, 13, 8, 12, 22, 2, 19, 26, 23, 21, 16, 4, 6, 1, 11, 18, 15, 5, 24, 20],
    ![0, 18, 26, 10, 13, 15, 2, 20, 11, 8, 14, 9, 5, 23, 3, 12, 27, 24, 22, 17, 21, 7, 1, 4, 19, 16, 6, 25],
    ![0, 19, 11, 27, 10, 14, 16, 3, 21, 4, 9, 15, 18, 6, 24, 2, 13, 20, 25, 23, 26, 22, 8, 1, 5, 12, 17, 7],
    ![0, 20, 4, 12, 24, 27, 7, 9, 3, 6, 21, 18, 8, 11, 23, 17, 1, 22, 13, 10, 16, 19, 15, 25, 2, 14, 5, 26],
    ![0, 21, 13, 5, 19, 25, 20, 8, 10, 2, 7, 22, 11, 9, 4, 24, 18, 1, 23, 14, 27, 17, 12, 16, 26, 3, 15, 6],
    ![0, 22, 6, 14, 23, 12, 26, 21, 9, 11, 3, 8, 15, 4, 10, 5, 25, 19, 1, 24, 7, 20, 18, 13, 17, 27, 2, 16],
    ![0, 23, 15, 7, 9, 24, 13, 27, 22, 10, 4, 2, 25, 16, 5, 11, 6, 26, 12, 1, 17, 8, 21, 19, 14, 18, 20, 3],
    ![0, 24, 8, 16, 3, 10, 25, 14, 20, 23, 11, 5, 1, 26, 17, 6, 4, 7, 27, 13, 2, 18, 9, 22, 12, 15, 19, 21],
    ![0, 25, 17, 9, 6, 2, 11, 26, 15, 21, 24, 4, 14, 1, 27, 18, 7, 5, 8, 20, 22, 3, 19, 10, 23, 13, 16, 12],
    ![0, 26, 10, 18, 5, 7, 3, 4, 27, 16, 22, 25, 21, 15, 1, 20, 19, 8, 6, 9, 13, 23, 2, 12, 11, 24, 14, 17],
    ![0, 27, 19, 11, 26, 6, 8, 2, 5, 20, 17, 23, 10, 22, 16, 1, 21, 12, 9, 7, 18, 14, 24, 3, 13, 4, 25, 15]]

/-- The desired reciprocal formula in orbit coordinates. -/
private def reciprocalTable : B → B :=
  ![1, 0, 3, 2, 4, 9, 6, 11, 8, 5, 10, 7, 27, 24, 21, 26, 23, 20, 25, 22, 17, 14, 19, 16, 13, 18, 15, 12]

private theorem point_reciprocal : ∀ b : B,
    point (reciprocalTable b) = swapPerm (point b) := by decide +kernel

private def value (b : B) : Root := (point b).getD 1

private theorem point_shift : ∀ a b : B,
    point (shift a b) = rootPerm (value a) (point b) := by decide +kernel

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

private theorem involutive_of_square (τ : Equiv.Perm Point) (hsq : τ ^ 2 = 1) :
    Function.Involutive τ := by
  intro p
  have h := congrArg (fun s : Equiv.Perm Point => s p) hsq
  simpa [pow_two, Equiv.Perm.mul_apply] using h

private theorem twist (τ : Equiv.Perm Point) (hsq : τ ^ 2 = 1)
    (hc : τ⁻¹ * linear * τ = linear ^ 5) : SemiconjBy τ linear (linear ^ 5) := by
  have hh : τ * τ = 1 := by simpa [pow_two] using hsq
  have hi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hh
  change τ * linear = linear ^ 5 * τ
  calc
    τ * linear = (τ⁻¹ * linear * τ) * τ := by rw [hi, mul_assoc (τ * linear), hh, mul_one]
    _ = linear ^ 5 * τ := by rw [hc]

private theorem twist_apply (τ : Equiv.Perm Point) (hsq : τ ^ 2 = 1)
    (hc : τ⁻¹ * linear * τ = linear ^ 5) (n : ℕ) (p : Point) :
    τ ((linear ^ n) p) = ((linear ^ 5) ^ n) (τ p) := by
  exact congrArg (fun s : Equiv.Perm Point => s p) ((twist τ hsq hc).pow_right n)

private theorem short_test : ∀ b : B,
    point b ≠ none → point b ≠ some 1 →
    ((linear ^ 5) ^ (2 : ℕ)) (point b) = point b →
    ∃ a : Fin 2, b = ⟨2 + a.val, by omega⟩ := by decide +kernel

private theorem short_image (τ : Equiv.Perm Point) (hsq : τ ^ 2 = 1)
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

private def code (τ : Equiv.Perm Point) (a : Fin 2) : Code :=
  (a, unpoint (τ (point 4)), unpoint (τ (point 12)), unpoint (τ (point 20)))

private theorem apply_code (τ : Equiv.Perm Point) (hsq : τ ^ 2 = 1)
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
private def reciprocalCandidate (c : Code) : Prop :=
  (∀ x : B, applyCode c x = reciprocalTable x) ∨
  (∀ x : B, applyCode c x = rotate 4 (reciprocalTable x))
private instance (c : Code) : Decidable (reciprocalCandidate c) :=
  inferInstanceAs (Decidable ((_ : Prop) ∨ (_ : Prop)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem certificate_zero : ∀ b c d : B, good (0,b,c,d) →
    (∃ n : Fin 8, ∀ x : B,
      word (0,b,c,d) x = shift (word (0,b,c,d) 1) (rotate n.val x)) →
    reciprocalCandidate (0,b,c,d) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem certificate_one : ∀ b c d : B, good (1,b,c,d) →
    (∃ n : Fin 8, ∀ x : B,
      word (1,b,c,d) x = shift (word (1,b,c,d) 1) (rotate n.val x)) →
    reciprocalCandidate (1,b,c,d) := by decide +kernel

private theorem certificate (c : Code) (hg : good c)
    (hw : ∃ n : Fin 8, ∀ x : B, word c x = shift (word c 1) (rotate n.val x)) :
    reciprocalCandidate c := by
  rcases c with ⟨a, b, c, d⟩
  fin_cases a
  · exact certificate_zero b c d hg hw
  · exact certificate_one b c d hg hw

private theorem good_code (τ : Equiv.Perm Point) (hsq : τ ^ 2 = 1)
    (hn : τ none = some 1) (hc : τ⁻¹ * linear * τ = linear ^ 5)
    (a : Fin 2) (ha : unpoint (τ (point 2)) = ⟨2 + a.val, by omega⟩) :
    good (code τ a) := by
  have hi (b : B) : applyCode (code τ a) (applyCode (code τ a) b) = b := by
    apply point_injective
    rw [apply_code τ hsq hn hc a ha, apply_code τ hsq hn hc a ha,
      involutive_of_square τ hsq]
  exact ⟨hi 4, hi 12, hi 20⟩

private theorem point_word (τ : Equiv.Perm Point) (hsq : τ ^ 2 = 1)
    (hn : τ none = some 1) (hc : τ⁻¹ * linear * τ = linear ^ 5)
    (a : Fin 2) (ha : unpoint (τ (point 2)) = ⟨2 + a.val, by omega⟩)
    (z : Root) (hz : τ (some u) = some z) (b : B) :
    point (word (code τ a) b) =
      (τ * rootPerm z⁻¹ * τ * rootPerm u * τ)
        (point b) := by
  have hv : value (applyCode (code τ a) 4) = z := by
    unfold value
    rw [apply_code τ hsq hn hc a ha]
    change (τ (some u)).getD 1 = z
    rw [hz]
    rfl
  rw [word, apply_code τ hsq hn hc a ha, point_shift, value_neg, hv,
    apply_code τ hsq hn hc a ha, point_shift, apply_code τ hsq hn hc a ha]
  rfl

private theorem linear_one : ∀ n : Fin 8, (linear ^ n.val) (some 1) = some 1 := by
  decide +kernel

private theorem swap_eq_of_word_affine (τ : Equiv.Perm Point) (hsq : τ ^ 2 = 1)
    (hn : τ none = some 1) (hc : τ⁻¹ * linear * τ = linear ^ 5)
    (z : Root) (hz : τ (some u) = some z)
    (v : Root) (n : Fin 8)
    (heq : τ * rootPerm z⁻¹ * τ * rootPerm u * τ = rootPerm v * linear ^ n.val) :
    τ = swapPerm ∨ τ = linear ^ 4 * swapPerm := by
  obtain ⟨a, ha⟩ := short_image τ hsq hn hc
  have hv : value (word (code τ a) 1) = v := by
    unfold value
    rw [point_word τ hsq hn hc a ha z hz, heq]
    change ((rootPerm v * linear ^ n.val) (some 1)).getD 1 = v
    rw [Equiv.Perm.mul_apply, linear_one n]
    change (some (v * 1)).getD 1 = v
    simp
  have hw : ∀ x : B, word (code τ a) x = shift (word (code τ a) 1) (rotate n.val x) := by
    intro x
    apply point_injective
    rw [point_word τ hsq hn hc a ha z hz, heq, point_shift, hv, point_rotate n]
    rfl
  rcases certificate (code τ a) (good_code τ hsq hn hc a ha) ⟨n, hw⟩ with h0 | h4
  · left
    apply Equiv.ext
    intro p
    rw [← point_unpoint p, ← apply_code τ hsq hn hc a ha, h0, point_reciprocal]
  · right
    apply Equiv.ext
    intro p
    rw [← point_unpoint p, ← apply_code τ hsq hn hc a ha, h4,
      point_rotate ⟨4, by decide⟩, point_reciprocal]
    rfl

/-- The affine stabilizer forces the concrete reciprocal permutation to belong
 to the subgroup containing the roots, scalar torus, and swapping involution. -/
public theorem swap_mem (L : Subgroup (Equiv.Perm Point))
    (htrans : ∀ v : Root, rootPerm v ∈ L)
    (hlinear : torusPerm scalar ∈ L)
    (haff : ∀ s : Equiv.Perm Point, s ∈ L → s none = none →
      ∃ (v : Root) (n : Fin 8), s = rootPerm v * torusPerm scalar ^ n.val)
    (τ : Equiv.Perm Point) (hτ : τ ∈ L) (hsq : τ ^ 2 = 1)
    (hn : τ none = some 1)
    (hc : τ⁻¹ * torusPerm scalar * τ = torusPerm scalar ^ 5) : swapPerm ∈ L := by
  have hi := involutive_of_square τ hsq
  have hz0 : τ (some 1) = none := by rw [← hn, hi]
  have hu : τ (some u) ≠ none := by
    intro h
    have h' := τ.injective (h.trans hz0.symm)
    exact (by decide : (some u : Point) ≠ some 1) h'
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp hu
  let W := τ * rootPerm z⁻¹ * τ * rootPerm u * τ
  have hW : W ∈ L := L.mul_mem (L.mul_mem (L.mul_mem (L.mul_mem hτ (htrans _)) hτ)
    (htrans _)) hτ
  have hfix : W none = none := by
    change τ (rootPerm z⁻¹ (τ (rootPerm u
      (τ none)))) = none
    rw [hn]
    change τ (rootPerm z⁻¹ (τ (some (u * 1)))) = none
    rw [mul_one, hz]
    change τ (some (z⁻¹ * z)) = none
    rw [inv_mul_cancel, hz0]
  obtain ⟨v, n, heq⟩ := haff W hW hfix
  rcases swap_eq_of_word_affine τ hsq hn hc z hz v n heq with he | he
  · exact he ▸ hτ
  · have hm := L.mul_mem (L.inv_mem (L.pow_mem hlinear 4)) hτ
    rw [he, linear, inv_mul_cancel_left] at hm
    exact hm
end UnitaryThree.SwapRigidity
