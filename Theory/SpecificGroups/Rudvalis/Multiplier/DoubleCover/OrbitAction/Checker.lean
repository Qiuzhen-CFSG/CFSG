module

public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.OrbitData
public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.Arithmetic
public import Mathlib.Algebra.Field.ZMod

/-!
# A checked arithmetic bridge for the marked Rudvalis projective action

For each label, a finite natural-number dot product checks the ordinary
matrix-vector product against a scalar multiple of the vector at the literal
permutation image. Reduction modulo five and `dotNat_cast` give the vector
equation. The scalar's checked nonzero residue supplies an actual unit.

The checker reads the published orbit blocks and twelve-bit inverse-convention
permutation maps directly. It changes neither matrix entries nor point labels.
Source: ATLAS `2RuG1-f5r28B0` and `RuG1-p4060B0`; see `../source/README.md`.
-/

namespace Rudvalis.Multiplier.DoubleCover.OrbitAction
public section

@[expose] def vectorEntry (v j : ℕ) : ℕ := (v >>> (3*j)) % 8

@[expose] def decodeVector (v : ℕ) : Vec := fun j => (vectorEntry v j.val : ZMod 5)

@[expose] def checkLine (m v w s : ℕ) : Bool :=
  (s % 5 != 0) && checkAll (fun j =>
    dotNat (entryNat m j) (vectorEntry v) 28 % 5 == (s * vectorEntry w j) % 5) 28

theorem checkLine_sound (m v w s : ℕ) (h : checkLine m v w s = true) :
    ∃ u : (ZMod 5)ˣ, (decodeMatrix m).mulVec (decodeVector v) =
      (u : ZMod 5) • decodeVector w := by
  simp only [checkLine, Bool.and_eq_true] at h
  obtain ⟨hs, hv⟩ := h
  have hs' : s % 5 ≠ 0 := by simpa only [bne_iff_ne] using hs
  have hn : (s : ZMod 5) ≠ 0 := by
    intro hz
    have hz' := congrArg ZMod.val hz
    exact hs' (by simpa using hz')
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine ⟨Units.mk0 (s : ZMod 5) hn, ?_⟩
  funext j
  have hj := (checkAll_spec _ _).mp hv j.val j.isLt
  have he : dotNat (entryNat m j.val) (vectorEntry v) 28 % 5 =
      (s * vectorEntry w j.val) % 5 := by simpa only [beq_iff_eq] using hj
  have hc := congrArg (fun n : ℕ => (n : ZMod 5)) he
  simp only [ZMod.natCast_mod, Nat.cast_mul, dotNat_cast] at hc
  exact hc

@[expose] def linePacked (i : ℕ) : ℕ := (lineBlocks[i / 128]!)[i % 128]!
@[expose] def pointMap (p i : ℕ) : ℕ := (p >>> (12 * i)) % 4096 % 4060

@[expose] def actionAt (m p i : ℕ) : Prop :=
  ∃ u : (ZMod 5)ˣ, (decodeMatrix m).mulVec (decodeVector (linePacked i)) =
    (u : ZMod 5) • decodeVector (linePacked (pointMap p i))

@[expose] def checkBlock (m p scalars first count : ℕ) : Bool :=
  checkAll (fun j => checkLine m (linePacked (first+j))
    (linePacked (pointMap p (first+j))) ((scalars >>> (2*j)) % 4 + 1)) count

theorem checkBlock_sound (m p scalars first count : ℕ)
    (h : checkBlock m p scalars first count = true) :
    ∀ j, j < count → actionAt m p (first+j) := by
  intro j hj
  exact checkLine_sound _ _ _ _ ((checkAll_spec _ _).mp h j hj)

/-- The 32 checked intervals cover exactly the published 4060 labels. -/
theorem action_of_blocks (m p : ℕ)
    (h : ∀ q : Fin 32, ∀ j, j < min 128 (4060 - 128 * q.val) →
      actionAt m p (128 * q.val + j)) (i : ℕ) (hi : i < 4060) :
    actionAt m p i := by
  have hq : i / 128 < 32 := by omega
  have hj : i % 128 < min 128 (4060 - 128 * (i / 128)) := by omega
  simpa only [Nat.div_add_mod] using h ⟨i / 128, hq⟩ (i % 128) hj

end
end Rudvalis.Multiplier.DoubleCover.OrbitAction
