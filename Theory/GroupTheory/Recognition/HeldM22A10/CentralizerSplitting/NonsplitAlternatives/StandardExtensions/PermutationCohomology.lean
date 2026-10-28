module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.Parity
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.Nonsplitting
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-!
# Factor sets for the ordinary binary permutation action

Every normalized factor set for the coordinate action of S4 on binary
four-space is equivalent to either zero or the diagonal parity carry.

An explicit degree-two cochain correction reduces the calculation to the
stabilizer of coordinate zero. We choose even transports from zero to each
coordinate, so the stabilizer parts have the same signs as the original
permutations. On that six-element stabilizer, twenty cocycle identities give
an explicit normalizing cochain and leave only the value on the square of
(23). That value lies in F2, giving the two alternatives. The finite tables
are checked by the kernel; the scalar identities are proved by linear
combinations of the cocycle equations.

This proves the ordinary-action cohomology step in the independent finite
extension argument for Huppert--Blackburn, *Finite Groups III*, XII.1.18(b),
p.314. The factor-set and equivalence conventions are exactly those of
`StandardExtensions.FactorSets`; no ambient-group or model-recognition
hypothesis enters the result.
-/

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions
open LocalModelDichotomy AbelianExtension

private abbrev coord (c : FactorSet permutationAction) (q r : SymmetricFour)
    (i : Fin 4) : ZMod 2 := (c.toFun q r).toAdd i

private theorem coord_cocycle (c : FactorSet permutationAction)
    (q r s : SymmetricFour) (i : Fin 4) :
    coord c q r i + coord c (q * r) s i =
      coord c r s (q.symm i) + coord c q (r * s) i :=
  congrArg (fun x : BinaryFour => x.toAdd i) (c.cocycle q r s)

-- Even transports ensure that the parity representative is unchanged.

private def transport (i : Fin 4) : SymmetricFour :=
  ![1, Equiv.swap 0 1 * Equiv.swap 1 2,
    Equiv.swap 0 2 * Equiv.swap 1 2, Equiv.swap 0 3 * Equiv.swap 1 2] i

private theorem transport_spec : ∀ i : Fin 4,
    transport i 0 = i ∧ Equiv.Perm.sign (transport i) = 1 := by decide +kernel

private def stabilizerPart (q : SymmetricFour) (i : Fin 4) : SymmetricFour :=
  (transport i)⁻¹ * q * transport (q.symm i)

private theorem stabilizerPart_fix (q : SymmetricFour) (i : Fin 4) :
    stabilizerPart q i 0 = 0 := by
  simp only [stabilizerPart, Equiv.Perm.mul_apply, (transport_spec _).1,
    Equiv.apply_symm_apply]
  exact (transport i).symm_apply_eq.mpr (transport_spec i).1.symm

private theorem stabilizerPart_mul (q r : SymmetricFour) (i : Fin 4) :
    stabilizerPart (q * r) i = stabilizerPart q i * stabilizerPart r (q.symm i) := by
  change (transport i)⁻¹ * (q * r) * transport (r.symm (q.symm i)) =
    ((transport i)⁻¹ * q * transport (q.symm i)) *
      ((transport (q.symm i))⁻¹ * r * transport (r.symm (q.symm i)))
  group

/-- The explicit correction comparing a cocycle with its restriction to the
point stabilizer. The minus sign also makes its value at the identity zero. -/
private def correction (c : FactorSet permutationAction) (q : SymmetricFour) (i : Fin 4) :
    ZMod 2 :=
  coord c (transport i)⁻¹ q 0 +
    coord c ((transport i)⁻¹ * q) (transport (q.symm i)) 0 -
    coord c (transport (q.symm i))⁻¹ (transport (q.symm i)) 0

private theorem correction_one (c : FactorSet permutationAction) (i : Fin 4) :
    correction c 1 i = 0 := by
  change coord c (transport i)⁻¹ 1 0 +
    coord c ((transport i)⁻¹ * 1) (transport i) 0 -
    coord c (transport i)⁻¹ (transport i) 0 = 0
  simp [coord, c.one_right]

/-- The degree-two restriction comparison, proved from five cocycle identities. -/
private theorem correction_identity (c : FactorSet permutationAction)
    (q r : SymmetricFour) (i : Fin 4) :
    coord c q r i + correction c (q * r) i =
      correction c q i + correction c r (q.symm i) +
        coord c (stabilizerPart q i) (stabilizerPart r (q.symm i)) 0 := by
  let a := (transport i)⁻¹
  let j := q.symm i
  let k := r.symm j
  let b := transport j
  let d := transport k
  have ha : a.symm 0 = i := (transport_spec i).1
  have hab : (a * q).symm 0 = j := by
    change q.symm (a.symm 0) = j
    rw [ha]
  have hb : b⁻¹.symm 0 = j := (transport_spec j).1
  have h1 := coord_cocycle c a q r 0
  have h2 := coord_cocycle c (a * q) b (b⁻¹ * r * d) 0
  have h3 := coord_cocycle c (a * q) r d 0
  have h4 := coord_cocycle c b⁻¹ r d 0
  have h5 := coord_cocycle c b⁻¹ b (b⁻¹ * r * d) 0
  have hcancel : b * (b⁻¹ * r * d) = r * d := by group
  rw [ha] at h1
  rw [hab, hcancel] at h2
  rw [hab] at h3
  rw [hb] at h4
  rw [hb, inv_mul_cancel, hcancel] at h5
  have hone : coord c 1 (b⁻¹ * r * d) 0 = 0 := by simp [coord, c.one_left]
  rw [hone] at h5
  change coord c q r i +
      (coord c a (q * r) 0 + coord c (a * (q * r)) d 0 - coord c d⁻¹ d 0) =
    (coord c a q 0 + coord c (a * q) b 0 - coord c b⁻¹ b 0) +
    (coord c b⁻¹ r 0 + coord c (b⁻¹ * r) d 0 - coord c d⁻¹ d 0) +
    coord c (a * q * b) (b⁻¹ * r * d) 0
  rw [← mul_assoc a q r]
  linear_combination -h1 - h2 + h3 - h4 + h5

-- Lexicographic enumeration of the permutations of {1, 2, 3}.

private def mul6 (i j : Fin 6) : Fin 6 :=
  ![![0, 1, 2, 3, 4, 5],
    ![1, 0, 4, 5, 2, 3],
    ![2, 3, 0, 1, 5, 4],
    ![3, 2, 5, 4, 0, 1],
    ![4, 5, 1, 0, 3, 2],
    ![5, 4, 3, 2, 1, 0]] i j

private def odd6 (i : Fin 6) : Bool := ![false, true, true, false, false, true] i

/-- Scalar cocycles on S3, with the correcting cochain zero at (23).
The remaining scalar is the value of the cocycle on ((23), (23)). -/
private theorem six_cocycle_classes (f : Fin 6 → Fin 6 → ZMod 2)
    (hl : ∀ j, f 0 j = 0) (hr : ∀ i, f i 0 = 0)
    (hc : ∀ i j k, f i j + f (mul6 i j) k = f j k + f i (mul6 j k)) :
    ∃ (z : ZMod 2) (d : Fin 6 → ZMod 2), d 0 = 0 ∧
      ∀ i j, f i j + d (mul6 i j) = d i + d j +
        if odd6 i && odd6 j then z else 0 := by
  have h112 : f 1 1 + f 0 2 = f 1 2 + f 1 4 := hc 1 1 2
  have h113 : f 1 1 + f 0 3 = f 1 3 + f 1 5 := hc 1 1 3
  have h121 : f 1 2 + f 4 1 = f 2 1 + f 1 3 := hc 1 2 1
  have h122 : f 1 2 + f 4 2 = f 2 2 + f 1 0 := hc 1 2 2
  have h123 : f 1 2 + f 4 3 = f 2 3 + f 1 1 := hc 1 2 3
  have h124 : f 1 2 + f 4 4 = f 2 4 + f 1 5 := hc 1 2 4
  have h125 : f 1 2 + f 4 5 = f 2 5 + f 1 4 := hc 1 2 5
  have h131 : f 1 3 + f 5 1 = f 3 1 + f 1 2 := hc 1 3 1
  have h132 : f 1 3 + f 5 2 = f 3 2 + f 1 5 := hc 1 3 2
  have h133 : f 1 3 + f 5 3 = f 3 3 + f 1 4 := hc 1 3 3
  have h134 : f 1 3 + f 5 4 = f 3 4 + f 1 0 := hc 1 3 4
  have h135 : f 1 3 + f 5 5 = f 3 5 + f 1 1 := hc 1 3 5
  have h211 : f 2 1 + f 3 1 = f 1 1 + f 2 0 := hc 2 1 1
  have h212 : f 2 1 + f 3 2 = f 1 2 + f 2 4 := hc 2 1 2
  have h213 : f 2 1 + f 3 3 = f 1 3 + f 2 5 := hc 2 1 3
  have h214 : f 2 1 + f 3 4 = f 1 4 + f 2 2 := hc 2 1 4
  have h215 : f 2 1 + f 3 5 = f 1 5 + f 2 3 := hc 2 1 5
  have h221 : f 2 2 + f 0 1 = f 2 1 + f 2 3 := hc 2 2 1
  have h224 : f 2 2 + f 0 4 = f 2 4 + f 2 5 := hc 2 2 4
  have h241 : f 2 4 + f 5 1 = f 4 1 + f 2 5 := hc 2 4 1
  simp only [hl, hr] at h112 h113 h122 h134 h211 h221 h224
  refine ⟨f 1 1, ![0, 0, f 1 2 + f 1 3 + f 2 1 + f 2 4,
    f 1 1 + f 1 2 + f 1 3 + f 2 4, f 1 1 + f 1 3 + f 2 1 + f 2 4,
    f 1 1 + f 1 2 + f 2 4], rfl, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · change f 0 0 + 0 = 0 + 0 + 0
    linear_combination (hl 0)
  · change f 0 1 + 0 = 0 + 0 + 0
    linear_combination (hl 1)
  · change f 0 2 + (f 1 2 + f 1 3 + f 2 1 + f 2 4) = 0 + (f 1 2 + f 1 3 + f 2 1 + f 2 4) + 0
    linear_combination (hl 2)
  · change f 0 3 + (f 1 1 + f 1 2 + f 1 3 + f 2 4) = 0 + (f 1 1 + f 1 2 + f 1 3 + f 2 4) + 0
    linear_combination (hl 3)
  · change f 0 4 + (f 1 1 + f 1 3 + f 2 1 + f 2 4) = 0 + (f 1 1 + f 1 3 + f 2 1 + f 2 4) + 0
    linear_combination (hl 4)
  · change f 0 5 + (f 1 1 + f 1 2 + f 2 4) = 0 + (f 1 1 + f 1 2 + f 2 4) + 0
    linear_combination (hl 5)
  · change f 1 0 + 0 = 0 + 0 + 0
    linear_combination (hr 1)
  · change f 1 1 + 0 = 0 + 0 + f 1 1
    linear_combination
  · change f 1 2 + (f 1 1 + f 1 3 + f 2 1 + f 2 4) = 0 + (f 1 2 + f 1 3 + f 2 1 + f 2 4) + f 1 1
    linear_combination
  · change f 1 3 + (f 1 1 + f 1 2 + f 2 4) = 0 + (f 1 1 + f 1 2 + f 1 3 + f 2 4) + 0
    linear_combination
  · change f 1 4 + (f 1 2 + f 1 3 + f 2 1 + f 2 4) = 0 + (f 1 1 + f 1 3 + f 2 1 + f 2 4) + 0
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h112
  · change f 1 5 + (f 1 1 + f 1 2 + f 1 3 + f 2 4) = 0 + (f 1 1 + f 1 2 + f 2 4) + f 1 1
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h113
  · change f 2 0 + (f 1 2 + f 1 3 + f 2 1 + f 2 4) = (f 1 2 + f 1 3 + f 2 1 + f 2 4) + 0 + 0
    linear_combination (hr 2)
  · change f 2 1 + (f 1 1 + f 1 2 + f 1 3 + f 2 4) = (f 1 2 + f 1 3 + f 2 1 + f 2 4) + 0 + f 1 1
    linear_combination
  · change f 2 2 + 0 = (f 1 2 + f 1 3 + f 2 1 + f 2 4) + (f 1 2 + f 1 3 + f 2 1 + f 2 4) + f 1 1
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide]))
      h121 + h131 + h211 + h224 + h241
  · change f 2 3 + 0 = (f 1 2 + f 1 3 + f 2 1 + f 2 4) + (f 1 1 + f 1 2 + f 1 3 + f 2 4) + 0
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide]))
      h121 + h131 + h211 + h221 + h224 + h241
  · change f 2 4 + (f 1 1 + f 1 2 + f 2 4) =
      (f 1 2 + f 1 3 + f 2 1 + f 2 4) + (f 1 1 + f 1 3 + f 2 1 + f 2 4) + 0
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide]))
  · change f 2 5 + (f 1 1 + f 1 3 + f 2 1 + f 2 4) =
      (f 1 2 + f 1 3 + f 2 1 + f 2 4) + (f 1 1 + f 1 2 + f 2 4) + f 1 1
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide]))
      h121 + h131 + h211 + h241
  · change f 3 0 + (f 1 1 + f 1 2 + f 1 3 + f 2 4) = (f 1 1 + f 1 2 + f 1 3 + f 2 4) + 0 + 0
    linear_combination (hr 3)
  · change f 3 1 + (f 1 2 + f 1 3 + f 2 1 + f 2 4) = (f 1 1 + f 1 2 + f 1 3 + f 2 4) + 0 + 0
    linear_combination h211
  · change f 3 2 + (f 1 1 + f 1 2 + f 2 4) =
      (f 1 1 + f 1 2 + f 1 3 + f 2 4) + (f 1 2 + f 1 3 + f 2 1 + f 2 4) + 0
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h212
  · change f 3 3 + (f 1 1 + f 1 3 + f 2 1 + f 2 4) =
      (f 1 1 + f 1 2 + f 1 3 + f 2 4) + (f 1 1 + f 1 2 + f 1 3 + f 2 4) + 0
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide]))
      h121 + h131 + h211 + h213 + h241
  · change f 3 4 + 0 = (f 1 1 + f 1 2 + f 1 3 + f 2 4) + (f 1 1 + f 1 3 + f 2 1 + f 2 4) + 0
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide]))
      h112 + h121 + h131 + h211 + h214 + h224 + h241
  · change f 3 5 + 0 = (f 1 1 + f 1 2 + f 1 3 + f 2 4) + (f 1 1 + f 1 2 + f 2 4) + 0
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide]))
      h113 + h121 + h131 + h211 + h215 + h221 + h224 + h241
  · change f 4 0 + (f 1 1 + f 1 3 + f 2 1 + f 2 4) = (f 1 1 + f 1 3 + f 2 1 + f 2 4) + 0 + 0
    linear_combination (hr 4)
  · change f 4 1 + (f 1 1 + f 1 2 + f 2 4) = (f 1 1 + f 1 3 + f 2 1 + f 2 4) + 0 + 0
    linear_combination h121
  · change f 4 2 + 0 = (f 1 1 + f 1 3 + f 2 1 + f 2 4) + (f 1 2 + f 1 3 + f 2 1 + f 2 4) + 0
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide]))
      h121 + h122 + h131 + h211 + h224 + h241
  · change f 4 3 + 0 = (f 1 1 + f 1 3 + f 2 1 + f 2 4) + (f 1 1 + f 1 2 + f 1 3 + f 2 4) + 0
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide]))
      h121 + h123 + h131 + h211 + h221 + h224 + h241
  · change f 4 4 + (f 1 1 + f 1 2 + f 1 3 + f 2 4) =
      (f 1 1 + f 1 3 + f 2 1 + f 2 4) + (f 1 1 + f 1 3 + f 2 1 + f 2 4) + 0
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h113 + h124
  · change f 4 5 + (f 1 2 + f 1 3 + f 2 1 + f 2 4) =
      (f 1 1 + f 1 3 + f 2 1 + f 2 4) + (f 1 1 + f 1 2 + f 2 4) + 0
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide]))
      h112 + h121 + h125 + h131 + h211 + h241
  · change f 5 0 + (f 1 1 + f 1 2 + f 2 4) = (f 1 1 + f 1 2 + f 2 4) + 0 + 0
    linear_combination (hr 5)
  · change f 5 1 + (f 1 1 + f 1 3 + f 2 1 + f 2 4) = (f 1 1 + f 1 2 + f 2 4) + 0 + f 1 1
    linear_combination h131 + h211
  · change f 5 2 + (f 1 1 + f 1 2 + f 1 3 + f 2 4) =
      (f 1 1 + f 1 2 + f 2 4) + (f 1 2 + f 1 3 + f 2 1 + f 2 4) + f 1 1
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide]))
      h113 + h132 + h212
  · change f 5 3 + (f 1 2 + f 1 3 + f 2 1 + f 2 4) =
      (f 1 1 + f 1 2 + f 2 4) + (f 1 1 + f 1 2 + f 1 3 + f 2 4) + 0
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide]))
      h112 + h121 + h131 + h133 + h211 + h213 + h241
  · change f 5 4 + 0 = (f 1 1 + f 1 2 + f 2 4) + (f 1 1 + f 1 3 + f 2 1 + f 2 4) + 0
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide]))
      h112 + h121 + h131 + h134 + h211 + h214 + h224 + h241
  · change f 5 5 + 0 = (f 1 1 + f 1 2 + f 2 4) + (f 1 1 + f 1 2 + f 2 4) + f 1 1
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide]))
      h113 + h121 + h131 + h135 + h211 + h215 + h221 + h224 + h241

-- Identify the table with the actual point stabilizer, including its signs.

private def sixAt (i : Fin 6) : SymmetricFour where
  toFun := ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3],
    ![0, 2, 3, 1], ![0, 3, 1, 2], ![0, 3, 2, 1]] i
  invFun := ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3],
    ![0, 3, 1, 2], ![0, 2, 3, 1], ![0, 3, 2, 1]] i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

private def sixIndex (q : SymmetricFour) : Fin 6 :=
  if q 1 = 1 then (if q 2 = 2 then 0 else 1) else
    if q 1 = 2 then (if q 2 = 1 then 2 else 3) else
      if q 2 = 1 then 4 else 5

private theorem sixAt_one : sixAt 0 = 1 := by decide +kernel

private theorem sixAt_fix : ∀ i, (sixAt i).symm 0 = 0 := by decide +kernel

private theorem sixAt_mul : ∀ i j, sixAt (mul6 i j) = sixAt i * sixAt j := by
  decide +kernel

private theorem sixIndex_at : ∀ i, sixIndex (sixAt i) = i := by decide +kernel

private theorem sixAt_cover : ∀ q : SymmetricFour, q 0 = 0 → sixAt (sixIndex q) = q := by
  decide +kernel

private theorem sixAt_parity : ∀ i j,
    (odd6 i && odd6 j) =
      decide (¬ (Equiv.Perm.sign (sixAt i) = 1 ∨ Equiv.Perm.sign (sixAt j) = 1)) := by
  decide +kernel

private theorem stabilizer_cocycle_classes (c : FactorSet permutationAction) :
    ∃ (z : ZMod 2) (d : SymmetricFour → ZMod 2), d 1 = 0 ∧
      ∀ q r : SymmetricFour, q 0 = 0 → r 0 = 0 →
        coord c q r 0 + d (q * r) = d q + d r +
          if Equiv.Perm.sign q = 1 ∨ Equiv.Perm.sign r = 1 then 0 else z := by
  let f : Fin 6 → Fin 6 → ZMod 2 := fun i j => coord c (sixAt i) (sixAt j) 0
  have hl : ∀ j, f 0 j = 0 := by intro j; simp [f, sixAt_one, coord, c.one_left]
  have hr : ∀ i, f i 0 = 0 := by intro i; simp [f, sixAt_one, coord, c.one_right]
  have hc : ∀ i j k, f i j + f (mul6 i j) k = f j k + f i (mul6 j k) := by
    intro i j k
    simpa only [f, sixAt_mul, sixAt_fix] using coord_cocycle c (sixAt i) (sixAt j) (sixAt k) 0
  obtain ⟨z, d, hd0, hd⟩ := six_cocycle_classes f hl hr hc
  refine ⟨z, fun q => d (sixIndex q), ?_, ?_⟩
  · exact hd0
  · intro q r hq hr
    obtain ⟨i, rfl⟩ : ∃ i, sixAt i = q := ⟨sixIndex q, sixAt_cover q hq⟩
    obtain ⟨j, rfl⟩ : ∃ j, sixAt j = r := ⟨sixIndex r, sixAt_cover r hr⟩
    simpa only [f, ← sixAt_mul, sixIndex_at, sixAt_parity, decide_eq_true_eq,
      ite_not] using hd i j

private theorem stabilizerPart_one (i : Fin 4) : stabilizerPart 1 i = 1 := by
  change (transport i)⁻¹ * 1 * transport i = 1
  group

private theorem stabilizerPart_sign (q : SymmetricFour) (i : Fin 4) :
    Equiv.Perm.sign (stabilizerPart q i) = Equiv.Perm.sign q := by
  simp only [stabilizerPart, map_mul, map_inv, (transport_spec _).2,
    inv_one, one_mul, mul_one]

private theorem permutation_cocycle_normal_form (c : FactorSet permutationAction) :
    ∃ (z : ZMod 2) (b : SymmetricFour → BinaryFour), b 1 = 1 ∧
      ∀ (q r : SymmetricFour) (i : Fin 4),
        coord c q r i + (b (q * r)).toAdd i =
          (b q).toAdd i + (b r).toAdd (q.symm i) +
            if Equiv.Perm.sign q = 1 ∨ Equiv.Perm.sign r = 1 then 0 else z := by
  obtain ⟨z, d, hd0, hd⟩ := stabilizer_cocycle_classes c
  let b : SymmetricFour → BinaryFour := fun q =>
    Multiplicative.ofAdd (fun i => correction c q i + d (stabilizerPart q i))
  refine ⟨z, b, ?_, ?_⟩
  · apply Multiplicative.toAdd.injective
    funext i
    change correction c 1 i + d (stabilizerPart 1 i) = 0
    rw [correction_one, stabilizerPart_one, hd0, add_zero]
  · intro q r i
    have h := correction_identity c q r i
    have hs := hd (stabilizerPart q i) (stabilizerPart r (q.symm i))
      (stabilizerPart_fix q i) (stabilizerPart_fix r (q.symm i))
    rw [← stabilizerPart_mul, stabilizerPart_sign, stabilizerPart_sign] at hs
    change coord c q r i + (correction c (q * r) i + d (stabilizerPart (q * r) i)) =
      (correction c q i + d (stabilizerPart q i)) +
      (correction c r (q.symm i) + d (stabilizerPart r (q.symm i))) +
      if Equiv.Perm.sign q = 1 ∨ Equiv.Perm.sign r = 1 then 0 else z
    linear_combination h + hs

/-- Every factor set for the ordinary binary permutation action is equivalent
to the trivial factor set or the diagonal parity carry. -/
public theorem permutationFactorSet_classes (c : FactorSet permutationAction) :
    c.Equivalent (FactorSet.trivial permutationAction) ∨
      c.Equivalent permutationFactorSet := by
  obtain ⟨z, b, hb, h⟩ := permutation_cocycle_normal_form c
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
  rcases hz z with hz | hz
  · left
    refine ⟨b, hb, fun q r => ?_⟩
    apply Multiplicative.toAdd.injective
    funext i
    change coord c q r i + (b (q * r)).toAdd i =
      (b q).toAdd i + (b r).toAdd (q.symm i) + 0
    simpa only [hz, ite_self] using h q r i
  · right
    refine ⟨b, hb, fun q r => ?_⟩
    apply Multiplicative.toAdd.injective
    funext i
    have hp : (permutationFactorSet.toFun q r).toAdd i =
        if Equiv.Perm.sign q = 1 ∨ Equiv.Perm.sign r = 1 then 0 else 1 := by
      change (if Equiv.Perm.sign q = 1 ∨ Equiv.Perm.sign r = 1 then
        (1 : BinaryFour) else diagonal).toAdd i = _
      split_ifs <;> rfl
    change coord c q r i + (b (q * r)).toAdd i =
      (b q).toAdd i + (b r).toAdd (q.symm i) + (permutationFactorSet.toFun q r).toAdd i
    rw [hp]
    simpa only [hz] using h q r i

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions
