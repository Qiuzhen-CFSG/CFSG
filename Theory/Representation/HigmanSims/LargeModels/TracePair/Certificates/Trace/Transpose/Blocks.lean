module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace.Transpose.Routing

/-!
# From block certificates to the full packed transpose

A block contains 128 consecutive rows and 128 consecutive columns of one
coefficient plane. The routing theorem exchanges its two coordinates.
The seven-by-seven block cover recovers every entry of the degree-896 matrix,
separately for the coefficients of 1 and omega. All indexing is zero-based;
block `(r,s)` of the original is compared with block `(s,r)` of the candidate.

This semantic bridge is independent of the numerical witnesses. Its actual
HS application is in `../Transpose.lean`; see `source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace.Transpose


def block (p : Packed.Row → ℕ) (a : Packed.Mat) (r c : ℕ) : ℕ :=
  pack 128 p (128 * c) ((a.drop (128 * r)).take 128)

theorem testBit_block (p : Packed.Row → ℕ) (hp : p (0, 0) = 0)
    (a : Packed.Mat) (r c : ℕ) (i j : Fin 128) :
    (block p a r c).testBit (128 * i.val + j.val) =
      (p (a.getD (128 * r + i.val) (0, 0))).testBit (128 * c + j.val) := by
  rw [block, testBit_pack p hp _ _ _ _ j.isLt, getD_block _ _ _ i.isLt]

def checkBlock (b c : Packed.Mat) (r s : ℕ) : Bool :=
  (permute stages128 (block Prod.fst b r s) == block Prod.fst c s r) &&
  (permute stages128 (block Prod.snd b r s) == block Prod.snd c s r)

theorem block_bits (p : Packed.Row → ℕ) (hp : p (0, 0) = 0)
    (b c : Packed.Mat) (r s : ℕ)
    (h : permute stages128 (block p b r s) = block p c s r) (i j : Fin 128) :
    (p (b.getD (128 * r + i.val) (0, 0))).testBit (128 * s + j.val) =
      (p (c.getD (128 * s + j.val) (0, 0))).testBit (128 * r + i.val) := by
  have hb := congrArg (fun n : ℕ => n.testBit (128 * j.val + i.val)) h
  simpa only [testBit_transpose, testBit_block p hp] using hb

theorem eval_eq_transpose (b c : Packed.Mat)
    (h : ∀ r s : Fin 7, checkBlock b c r.val s.val = true) :
    Packed.eval 896 c = (Packed.eval 896 b).transpose := by
  funext i j
  let r : Fin 7 := ⟨j.val / 128, by omega⟩
  let s : Fin 7 := ⟨i.val / 128, by omega⟩
  let u : Fin 128 := ⟨j.val % 128, Nat.mod_lt _ (by decide)⟩
  let v : Fin 128 := ⟨i.val % 128, Nat.mod_lt _ (by decide)⟩
  have hj : 128 * r.val + u.val = j.val := by dsimp [r, u]; omega
  have hi : 128 * s.val + v.val = i.val := by dsimp [s, v]; omega
  have hb := h r s
  simp only [checkBlock, Bool.and_eq_true, beq_iff_eq] at hb
  have h₀ := block_bits Prod.fst rfl b c r.val s.val hb.1 u v
  have h₁ := block_bits Prod.snd rfl b c r.val s.val hb.2 u v
  rw [hi, hj] at h₀ h₁
  change Packed.decode (c.getD i.val (0, 0)) j.val =
    Packed.decode (b.getD j.val (0, 0)) i.val
  unfold Packed.decode Packed.Base.entry
  unfold Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit
  rw [h₀, h₁]


end Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace.Transpose
