module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Arithmetic
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Packing

/-!
# Soundness of the Fi22 root-action check

The checker compares packed coordinates for the literal shared root words, with
three possible nonzero scalars. Its soundness theorem returns exactly the
quadratic-field vector equality needed by the labeling assembly. The ambient
fixed-point guard retains all 694 labels, including label 1982.

Source: ATLAS F22G1-p3510B0 and GLS3 Table 5.3t.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi22.TransvectionComparison.Labeling.ActionTable
open KernelCertificate
open Arithmetic

def pairCheck (x y : Fin 3510) : Bool :=
  let z := packedCoordinate (Generation.rootAction x y)
  let t := trans (packedCoordinate x) (packedCoordinate y)
  z == t || mul (2 * 1365) z == t || mul (3 * 1365) z == t

def rowCheck (x : Fin 3510) (n : Nat) : Bool :=
  let y : Fin 3510 := ⟨n % 3510, Nat.mod_lt _ (by decide)⟩
  if fastA y = y then pairCheck x y else true

/-- The same evaluator as `Generation.rootAction`, with its word code supplied. -/
def codeAction (code : Nat) (y : Fin 3510) : Fin 3510 :=
  let bs := code.bits.dropLast
  bs.foldr Generation.backwardLetter
    (fastA (bs.foldl (fun y b => Generation.forwardLetter b y) y))

/-- Specializing the two constant inputs avoids repeated table lookup per pair. -/
def codeRowCheck (code v : Nat) (n : Nat) : Bool :=
  let y : Fin 3510 := ⟨n % 3510, Nat.mod_lt _ (by decide)⟩
  if fastA y = y then
    let z := packedCoordinate (codeAction code y)
    let t := trans v (packedCoordinate y)
    z == t || mul (2 * 1365) z == t || mul (3 * 1365) z == t
  else true

private theorem vector_scale (s : Nat) (hs : s < 4) (z : Nat) :
    vector (mul (s * 1365) z) = digit s • vector z := by
  rw [vector_mul, vector_replicate ⟨s, hs⟩]
  rfl

theorem pairCheck_sound (x y : Fin 3510) (h : pairCheck x y = true) :
    ∃ c : Four, c ≠ 0 ∧ c • representative (Generation.rootAction x y) =
      transvection (representative x) (representative y) := by
  simp only [pairCheck, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (h | h) | h
  · refine ⟨1, one_ne_zero, ?_⟩
    simpa only [one_smul, vector_trans, packedCoordinate_eq, representative] using congrArg vector h
  · refine ⟨digit 2, by decide +kernel, ?_⟩
    simpa only [vector_scale 2 (by decide), vector_trans, packedCoordinate_eq, representative] using
      congrArg vector h
  · refine ⟨digit 3, by decide +kernel, ?_⟩
    simpa only [vector_scale 3 (by decide), vector_trans, packedCoordinate_eq, representative] using
      congrArg vector h

theorem rowCheck_sound (x : Fin 3510) (h : BitNetwork.check (rowCheck x) 0 3510 = true)
    (y : Fin 3510) (hy : fastA y = y) :
    ∃ c : Four, c ≠ 0 ∧ c • representative (Generation.rootAction x y) =
      transvection (representative x) (representative y) := by
  apply pairCheck_sound
  have h' := BitNetwork.check_sound (rowCheck x) 0 3510 h y.val (Nat.zero_le _) y.isLt
  simpa only [rowCheck, Nat.mod_eq_of_lt y.isLt, if_pos hy] using h'

end Sporadic.Fischer.Fi22.TransvectionComparison.Labeling.ActionTable
