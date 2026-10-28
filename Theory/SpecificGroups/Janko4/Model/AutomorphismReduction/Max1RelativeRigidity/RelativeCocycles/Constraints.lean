module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.RelativeCocycles.Binary
import Mathlib.Tactic.FinCases
/-!
# Exhausting the two-generator relative cocycles

The first stabilizer word says that the displacement of x has mask zero or
three. For each of these two masks, the remaining four words leave precisely
mask zero or six for the displacement of y, and force the x mask to zero.

The exhaustive check is divided into 32 blocks of 64 y masks. Each block is
reduced by Lean's kernel; the executable discovery program and its proposed
row elimination are not part of the trust boundary. `WordSoundness` connects
these same recurrences and words to the actual ATLAS max1 subgroup.
-/
@[expose] public section
namespace Janko4.Max1RelativeRigidity.RelativeCocycles
private instance (z : V) : Decidable (Line z) := inferInstanceAs (Decidable (_ ∨ _))
private def Valid (m : Fin 2048) : Prop := ∀ t : Fin 2,
  let a : V := if t = 0 then 0 else 3
  let b : V := BitVec.ofNat 11 m.val
  (Line (wordDelta word1 a b) ∧ Line (wordDelta word2 a b) ∧
    Line (wordDelta word3 a b) ∧ Line (wordDelta word4 a b)) →
    a = 0 ∧ (b = 0 ∨ b = 6)
private instance (m : Fin 2048) : Decidable (Valid m) := by unfold Valid; infer_instance

set_option maxRecDepth 10000 in
private theorem block0 : ∀ j : Fin 64, Valid ⟨0 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block1 : ∀ j : Fin 64, Valid ⟨64 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block2 : ∀ j : Fin 64, Valid ⟨128 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block3 : ∀ j : Fin 64, Valid ⟨192 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block4 : ∀ j : Fin 64, Valid ⟨256 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block5 : ∀ j : Fin 64, Valid ⟨320 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block6 : ∀ j : Fin 64, Valid ⟨384 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block7 : ∀ j : Fin 64, Valid ⟨448 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block8 : ∀ j : Fin 64, Valid ⟨512 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block9 : ∀ j : Fin 64, Valid ⟨576 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block10 : ∀ j : Fin 64, Valid ⟨640 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block11 : ∀ j : Fin 64, Valid ⟨704 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block12 : ∀ j : Fin 64, Valid ⟨768 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block13 : ∀ j : Fin 64, Valid ⟨832 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block14 : ∀ j : Fin 64, Valid ⟨896 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block15 : ∀ j : Fin 64, Valid ⟨960 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block16 : ∀ j : Fin 64, Valid ⟨1024 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block17 : ∀ j : Fin 64, Valid ⟨1088 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block18 : ∀ j : Fin 64, Valid ⟨1152 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block19 : ∀ j : Fin 64, Valid ⟨1216 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block20 : ∀ j : Fin 64, Valid ⟨1280 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block21 : ∀ j : Fin 64, Valid ⟨1344 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block22 : ∀ j : Fin 64, Valid ⟨1408 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block23 : ∀ j : Fin 64, Valid ⟨1472 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block24 : ∀ j : Fin 64, Valid ⟨1536 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block25 : ∀ j : Fin 64, Valid ⟨1600 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block26 : ∀ j : Fin 64, Valid ⟨1664 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block27 : ∀ j : Fin 64, Valid ⟨1728 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block28 : ∀ j : Fin 64, Valid ⟨1792 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block29 : ∀ j : Fin 64, Valid ⟨1856 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block30 : ∀ j : Fin 64, Valid ⟨1920 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block31 : ∀ j : Fin 64, Valid ⟨1984 + j.val, by omega⟩ := by
  decide +kernel

private theorem valid_all (m : Fin 2048) : Valid m := by
  have h : ∀ i : Fin 32, ∀ j : Fin 64, Valid ⟨64 * i.val + j.val, by omega⟩ := by
    intro i
    fin_cases i
    · exact block0
    · exact block1
    · exact block2
    · exact block3
    · exact block4
    · exact block5
    · exact block6
    · exact block7
    · exact block8
    · exact block9
    · exact block10
    · exact block11
    · exact block12
    · exact block13
    · exact block14
    · exact block15
    · exact block16
    · exact block17
    · exact block18
    · exact block19
    · exact block20
    · exact block21
    · exact block22
    · exact block23
    · exact block24
    · exact block25
    · exact block26
    · exact block27
    · exact block28
    · exact block29
    · exact block30
    · exact block31
  convert h ⟨m.val / 64, by omega⟩ ⟨m.val % 64, Nat.mod_lt _ (by decide)⟩ using 1
  apply Fin.ext
  exact (Nat.div_add_mod m.val 64).symm

private theorem word0_delta (a b : V) : wordDelta word0 a b = a := by
  change actX 0 ^^^ a = a
  rw [show actX 0 = 0#11 from rfl]
  exact BitVec.zero_xor

/-- The five stabilizer-word conditions have exactly the principal-cocycle
possibilities `(dx,dy) = (0,0)` and `(0,6)`. -/
theorem five_word_constraints (a b : V)
    (h0 : Line (wordDelta word0 a b))
    (h1 : Line (wordDelta word1 a b))
    (h2 : Line (wordDelta word2 a b))
    (h3 : Line (wordDelta word3 a b))
    (h4 : Line (wordDelta word4 a b)) :
    a = 0 ∧ (b = 0 ∨ b = 6) := by
  rw [word0_delta] at h0
  rcases h0 with rfl | rfl
  · have h := valid_all ⟨b.toNat, b.isLt⟩ 0
    simp only [BitVec.ofNat_toNat] at h
    exact h ⟨h1, h2, h3, h4⟩
  · have h := valid_all ⟨b.toNat, b.isLt⟩ 1
    simp only [BitVec.ofNat_toNat, if_neg (by decide : (1 : Fin 2) ≠ 0)] at h
    exact h ⟨h1, h2, h3, h4⟩

end Janko4.Max1RelativeRigidity.RelativeCocycles
