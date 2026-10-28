module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.CosetAction.Data

/-!
# Certified byte evaluation of binary G₂ root words

The eight basis images of each root/Weyl map are checked in the kernel.
XOR decodes to addition in the octonion carrier, so linearity gives the action
on every byte. Every root/Weyl letter is an involution, and induction then
identifies inverse signed-word evaluation with the computational byte action.
This avoids repeatedly unfolding nested octonion linear maps in the flag
certificates. The words are required to use exponents ±1; that premise is
checked for every word used by GeometryData.

The basis bytes derive from the ATLAS root maps imported by Data; see its
attribution and LICENSES/ATLAS.txt. Source application: Aschbacher–Smith
G.7.2(3), printed p.348 / PDF p.359.
-/

@[expose] public section
open Atlas.G2 Atlas.SplitOctonion
open scoped Pointwise
namespace G2DerivedPermutationFiltration.CycleFlagCoordinates
open VertexCoordinates VertexCoordinates.ActionGeometry
set_option maxRecDepth 16000

def rootColumns : Fin 8 → Fin 8 → Fin 256 :=
  ![![1, 2, 4, 8, 16, 32, 65, 130],
    ![1, 2, 4, 8, 16, 33, 64, 132],
    ![1, 2, 4, 9, 17, 34, 68, 153],
    ![1, 2, 5, 10, 18, 32, 90, 160],
    ![1, 2, 6, 8, 16, 32, 96, 128],
    ![1, 3, 4, 12, 20, 60, 64, 192],
    ![1, 4, 2, 8, 16, 64, 32, 128],
    ![2, 1, 32, 16, 8, 4, 128, 64]]

def rootByte (j : Fin 8) (n : Fin 256) : Fin 256 :=
  (List.ofFn fun i : Fin 8 => if n.val.testBit i.val then rootColumns j i else 0).foldr
    (fun a b => a ^^^ b) 0

private theorem decode_zero : decode 0 = 0 := by
  funext i
  simp [decode]

private theorem decode_xor (a b : Fin 256) : decode (a ^^^ b) = decode a + decode b := by
  funext i
  simp only [decode, Pi.add_apply]
  change (if ((a.val ^^^ b.val) % 2^8).testBit i.val then (1 : ZMod 2) else 0) = _
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  simp only [show i.val < 8 from i.isLt, decide_true, Bool.true_and]
  cases a.val.testBit i.val <;> cases b.val.testBit i.val <;> decide

private theorem decode_fold (xs : List (Fin 256)) :
    decode (xs.foldr (fun a b => a ^^^ b) 0) = (xs.map decode).sum := by
  induction xs with
  | nil => exact decode_zero
  | cons a xs ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, decode_xor, ih]

private theorem root_basis_images : ∀ (j b : Fin 8),
    (rootGenerator j).val (Pi.single b 1) = decode (rootColumns j b) := by
  decide +kernel

/-- Linearity reduces the byte action to the eight checked basis images. -/
theorem rootByte_decode (j : Fin 8) (n : Fin 256) :
    rootGenerator j • decode n = decode (rootByte j n) := by
  have hn : decode n = ∑ b : Fin 8,
      (if n.val.testBit b.val then Pi.single b (1 : ZMod 2) else 0) := by
    symm
    calc
      _ = ∑ b : Fin 8, Pi.single b (decode n b) := by
        apply Finset.sum_congr rfl
        intro b _
        cases h : n.val.testBit b.val <;> simp [decode, h]
      _ = decode n := Finset.univ_sum_single _
  change (rootGenerator j).val (decode n) = _
  rw [hn, map_sum, rootByte, decode_fold, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro b _
  cases h : n.val.testBit b.val <;> simp [h, decode_zero, root_basis_images]



theorem rootGenerator_inv (j : Fin 8) : (rootGenerator j)⁻¹ = rootGenerator j := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.pi_ext
  have h : ∀ (i k : Fin 8) (a : ZMod 2),
      ((rootGenerator i)⁻¹).val (Pi.single k a) = (rootGenerator i).val (Pi.single k a) := by
    decide +kernel
  exact h j

def inverseBytes (w : List (Fin 8 × ℤ)) (n : Fin 256) : Fin 256 :=
  w.foldl (fun n a => rootByte a.1 n) n

theorem evalWord_inv_decode (w : List (Fin 8 × ℤ))
    (hw : ∀ a ∈ w, a.2 = 1 ∨ a.2 = -1) (n : Fin 256) :
    (evalWord w)⁻¹ • decode n = decode (inverseBytes w n) := by
  induction w generalizing n with
  | nil => simp [evalWord, inverseBytes]
  | cons a w ih =>
    have hp : (rootGenerator a.1 ^ a.2)⁻¹ = rootGenerator a.1 := by
      rcases hw a (by simp) with h | h
      · rw [h, zpow_one, rootGenerator_inv]
      · rw [h, zpow_neg_one, inv_inv]
    change (rootGenerator a.1 ^ a.2 * evalWord w)⁻¹ • decode n = _
    rw [mul_inv_rev, SemigroupAction.mul_smul, hp, rootByte_decode,
      ih (fun b hb => hw b (List.mem_cons_of_mem a hb))]
    rfl

theorem rootByte_finset (j : Fin 8) (s : Finset (Fin 256)) :
    rootGenerator j • s.image decode = (s.image (rootByte j)).image decode := by
  rw [Finset.smul_finset_def, Finset.image_image, Finset.image_image]
  congr 1
  funext n
  exact rootByte_decode j n

theorem inverseBytes_finset (w : List (Fin 8 × ℤ))
    (hw : ∀ a ∈ w, a.2 = 1 ∨ a.2 = -1) (s : Finset (Fin 256)) :
    (evalWord w)⁻¹ • s.image decode = (s.image (inverseBytes w)).image decode := by
  rw [Finset.smul_finset_def, Finset.image_image, Finset.image_image]
  congr 1
  funext n
  exact evalWord_inv_decode w hw n

end G2DerivedPermutationFiltration.CycleFlagCoordinates
