module

public import Theory.SpecificGroups.ReeTwo.SylowCollectedArithmetic

/-!
# Integer-encoded arithmetic for the Ree two Sylow model

Ten binary core coordinates and the cyclic-four coordinate encode an element
as a natural number. Decoding after encoding is the identity, so equality of
codes proves equality in the original group. Multiplication, inverse,
conjugation, and word evaluation on codes agree with those group operations.

The integer representation forces each intermediate product to a concrete value
before the next product is evaluated. This avoids large nested coordinate
expressions in kernel-checked finite certificates.

Source: the coordinates and collected operations of `SylowCollectedArithmetic`,
following Shinoda (1975), (2.3), pp. 81–82.
-/

@[expose] public section
namespace ReeTwo.SylowModel.Collected
open Theory.GroupTheory

def code (x : SylowModel) : Nat :=
  1 * x.left.b0.val + 2 * x.left.b1.val + 4 * x.left.b2.val + 8 * x.left.b3.val + 16 * x.left.b4.val + 32 * x.left.b5.val + 64 * x.left.b6.val + 128 * x.left.b7.val + 256 * x.left.b8.val + 512 * x.left.b9.val + 1024 * x.right.toAdd.val
def decode (n : Nat) : SylowModel :=
  ⟨⟨(n / 1 : Nat), (n / 2 : Nat), (n / 4 : Nat), (n / 8 : Nat), (n / 16 : Nat), (n / 32 : Nat), (n / 64 : Nat), (n / 128 : Nat), (n / 256 : Nat), (n / 512 : Nat)⟩, Multiplicative.ofAdd (n / 1024 : Nat)⟩

theorem decode_code (x : SylowModel) : decode (code x) = x := by
  have h0 := ZMod.val_lt x.left.b0
  have h1 := ZMod.val_lt x.left.b1
  have h2 := ZMod.val_lt x.left.b2
  have h3 := ZMod.val_lt x.left.b3
  have h4 := ZMod.val_lt x.left.b4
  have h5 := ZMod.val_lt x.left.b5
  have h6 := ZMod.val_lt x.left.b6
  have h7 := ZMod.val_lt x.left.b7
  have h8 := ZMod.val_lt x.left.b8
  have h9 := ZMod.val_lt x.left.b9
  have ht := ZMod.val_lt x.right.toAdd
  apply SemidirectProduct.ext
  · apply Core.ext <;> apply ZMod.val_injective <;>
      simp only [decode, code, ZMod.val_natCast] <;> omega
  · apply Multiplicative.toAdd.injective
    apply ZMod.val_injective
    change ((code x / 1024 : Nat) : ZMod 4).val = x.right.toAdd.val
    simp only [code, ZMod.val_natCast]
    omega

theorem code_injective : Function.Injective code := by
  intro x y h
  rw [← decode_code x, h, decode_code]

def packedMul (a b : Nat) : Nat := code (collectedMul (decode a) (decode b))
theorem packedMul_code (x y : SylowModel) :
    packedMul (code x) (code y) = code (x * y) := by
  simp only [packedMul, decode_code, collectedMul_eq]

def packedInv (a : Nat) : Nat := code (collectedInv (decode a))
theorem packedInv_code (x : SylowModel) : packedInv (code x) = code x⁻¹ := by
  simp only [packedInv, decode_code, collectedInv_eq]

def packedConj (a b : Nat) := packedMul (packedMul a b) (packedInv a)
theorem packedConj_code (x y : SylowModel) :
    packedConj (code x) (code y) = code (MulAut.conj x y) := by
  simp only [packedConj, packedMul_code, packedInv_code, MulAut.conj_apply]

def packedEval {n : Nat} (a : Fin n → Nat) : List (Fin n) → Nat
  | [] => code 1
  | k :: ks => packedMul (a k) (packedEval a ks)
theorem packedEval_code {n : Nat} (a : Fin n → SylowModel) (w : List (Fin n)) :
    packedEval (fun k => code (a k)) w = code (evalWord a w) := by
  induction w with
  | nil => rfl
  | cons k ks ih => simp only [packedEval, ih, packedMul_code, evalWord]
end ReeTwo.SylowModel.Collected
