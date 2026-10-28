module
public import Theory.SpecificGroups.ReeF4.DerivedTits.Realization.TransportComparison.BinaryProducts
-- Internal access to the already certified first relative-root table.
import all Theory.SpecificGroups.ReeF4.DerivedTits.Realization.TransportComparison.BinaryProducts

-- Intentional internal access to generated certificate data.
import all Theory.SpecificGroups.Tits.InvolutionRootGeometry.BinaryDerivedFusion.OuterSquares.Data

/-!
# Kernel-checked row paths for binary Ree outer squares

A packed binary row is interpreted as a vector in the established
52-dimensional representation. The checker certifies each shared transition
and then verifies the path for each normal form, applied twice. Its last row
differs in the first 52 bits, which rules out the identity matrix.

Only 2,030 distinct row transitions are needed for the 2,048 words. Packed
integer lookup and a single list traversal keep the kernel certificate small;
no full matrix square or unchecked computation enters the proof.

Source: Parrott (1972), §5, p.683; GLS3 Table 2.4 and 2.4.5(d).
The carrier comparison is assembled in the parent `OuterSquares.lean`.
-/

open ReeF4.DerivedTits.Realization
open ReeF4.DerivedTits.Realization.TransportComparison.Products
open Thompson.BinaryMatrix
open scoped Matrix
namespace Tits.InvolutionRootGeometry.BinaryDerivedFusion.OuterSquares

/-- The exact outer prefix followed by Parrott's ordered Sylow word. -/
@[expose] public def binaryWord (n : ℕ) : BinaryUnit :=
  relative 0 * (generator .s1 ^ (n % 2) * generator .s2 ^ (n / 2 % 2) *
    generator .s3 ^ (n / 4 % 4) * generator .s4 ^ (n / 16 % 2) *
    generator .s5 ^ (n / 32 % 4) * generator .s6 ^ (n / 128 % 2) *
    generator .s7 ^ (n / 256 % 4) * generator .s8 ^ (n / 1024 % 2))

private def letters (n : ℕ) : List (Fin 9) :=
  [0] ++ List.replicate (n % 2) 1 ++ List.replicate (n / 2 % 2) 2 ++
  List.replicate (n / 4 % 4) 3 ++ List.replicate (n / 16 % 2) 4 ++
  List.replicate (n / 32 % 4) 5 ++ List.replicate (n / 128 % 2) 6 ++
  List.replicate (n / 256 % 4) 7 ++ List.replicate (n / 1024 % 2) 8

private def rows : Fin 9 → Array ℕ :=
  ![relativeRows0, Binary.generatorRows .s1, Binary.generatorRows .s2,
    Binary.generatorRows .s3, Binary.generatorRows .s4, Binary.generatorRows .s5,
    Binary.generatorRows .s6, Binary.generatorRows .s7, Binary.generatorRows .s8]

private def bits (r : ℕ) : Fin 52 → ZMod 2 := fun j => bit r j.val

private theorem bits_rowProduct (r : ℕ) (a : Array ℕ) :
    bits (rowProduct r a 52) = bits r ᵥ* decode 52 a := by
  ext j
  exact (bit_rowProduct r a 52 j.val).trans
    (Fin.sum_univ_eq_sum_range (fun k => bit r k * bit a[k]! j.val) 52).symm

private theorem bits_fold (as : List (Array ℕ)) (r : ℕ) :
    bits (as.foldl (fun r a => rowProduct r a 52) r) =
      bits r ᵥ* (as.map (decode 52)).prod := by
  induction as generalizing r with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih,
      bits_rowProduct, Matrix.vecMul_vecMul]

private theorem letters_prod (n : ℕ) :
    (((letters n).map rows).map (decode 52)).prod = (binaryWord n).val := by
  simp [letters, rows, binaryWord, Units.val_pow_eq_pow_val,
    generator_val, relative_val_0, Binary.generatorMatrix, mul_assoc]

private theorem mod_eq_of_bits_eq {a b : ℕ} (h : bits a = bits b) :
    a % 2^52 = b % 2^52 := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow]
  by_cases hj : j < 52
  · simp only [hj, decide_true, Bool.true_and]
    have he := congrFun h ⟨j, hj⟩
    change bit a j = bit b j at he
    cases ha : a.testBit j <;> cases hb : b.testBit j <;> simp_all [bit]
  · simp [hj]

private abbrev Edge := Fin 9 × ℕ × ℕ

private def checkPath {k : ℕ} (edges : Fin k → Edge) :
    List (Fin 9) → ℕ → ℕ → List (Fin k) → Bool
  | [], a, b, [] => a % 2^52 != b % 2^52
  | l :: ls, a, b, i :: is =>
    (edges i).1 == l && (edges i).2.1 == a &&
      checkPath edges ls (edges i).2.2 b is
  | _, _, _, _ => false

private theorem checkPath_sound {k : ℕ} (edges : Fin k → Edge)
    (hE : ∀ i, rowProduct (edges i).2.1 (rows (edges i).1) 52 = (edges i).2.2)
    (ls : List (Fin 9)) (a b : ℕ) (is : List (Fin k))
    (h : checkPath edges ls a b is = true) :
    (ls.map rows).foldl (fun a m => rowProduct a m 52) a % 2^52 ≠ b % 2^52 := by
  induction ls generalizing a is with
  | nil =>
    cases is with
    | nil => simpa [checkPath] using h
    | cons => simp [checkPath] at h
  | cons l ls ih =>
    cases is with
    | nil => simp [checkPath] at h
    | cons i is =>
      simp only [checkPath, Bool.and_eq_true, beq_iff_eq] at h
      rw [List.map_cons, List.foldl_cons, ← h.1.1, ← h.1.2, hE i]
      exact ih _ is h.2

private def edgeAt (i : ℕ) : Edge :=
  let v := packedEdges >>> (108 * i)
  (⟨v % 16 % 9, Nat.mod_lt _ (by decide)⟩,
    (v >>> 4) % 2^52, (v >>> 56) % 2^52)

private def edges (i : Fin edgeCount) : Edge := edgeAt i.val

private def checkEdges (b : Fin edgeBatchCount) : Bool :=
  ((edgeData b).zipIdx (64 * b.val)).all (fun p =>
    edgeAt p.2 == p.1 && rowProduct p.1.2.1 (rows p.1.1) 52 == p.1.2.2)

-- Each kernel reduction and its elaboration have their own bounded batch.
-- Evaluate them sequentially to retain Lean's default memory and heartbeat limits.
set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_00 : checkEdges 0 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_01 : checkEdges 1 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_02 : checkEdges 2 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_03 : checkEdges 3 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_04 : checkEdges 4 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_05 : checkEdges 5 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_06 : checkEdges 6 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_07 : checkEdges 7 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_08 : checkEdges 8 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_09 : checkEdges 9 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_10 : checkEdges 10 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_11 : checkEdges 11 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_12 : checkEdges 12 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_13 : checkEdges 13 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_14 : checkEdges 14 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_15 : checkEdges 15 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_16 : checkEdges 16 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_17 : checkEdges 17 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_18 : checkEdges 18 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_19 : checkEdges 19 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_20 : checkEdges 20 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_21 : checkEdges 21 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_22 : checkEdges 22 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_23 : checkEdges 23 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_24 : checkEdges 24 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_25 : checkEdges 25 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_26 : checkEdges 26 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_27 : checkEdges 27 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_28 : checkEdges 28 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_29 : checkEdges 29 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_30 : checkEdges 30 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem edge_check_31 : checkEdges 31 = true := by decide +kernel

private theorem edges_checked (b : Fin edgeBatchCount) : checkEdges b = true := by
  fin_cases b
  · exact edge_check_00
  · exact edge_check_01
  · exact edge_check_02
  · exact edge_check_03
  · exact edge_check_04
  · exact edge_check_05
  · exact edge_check_06
  · exact edge_check_07
  · exact edge_check_08
  · exact edge_check_09
  · exact edge_check_10
  · exact edge_check_11
  · exact edge_check_12
  · exact edge_check_13
  · exact edge_check_14
  · exact edge_check_15
  · exact edge_check_16
  · exact edge_check_17
  · exact edge_check_18
  · exact edge_check_19
  · exact edge_check_20
  · exact edge_check_21
  · exact edge_check_22
  · exact edge_check_23
  · exact edge_check_24
  · exact edge_check_25
  · exact edge_check_26
  · exact edge_check_27
  · exact edge_check_28
  · exact edge_check_29
  · exact edge_check_30
  · exact edge_check_31

private theorem edgeData_length (b : Fin edgeBatchCount) :
    (edgeData b).length = min 64 (edgeCount - 64 * b.val) := by
  fin_cases b
  all_goals rfl

private theorem edges_valid (i : Fin edgeCount) :
    rowProduct (edges i).2.1 (rows (edges i).1) 52 = (edges i).2.2 := by
  let b : Fin edgeBatchCount := ⟨i.val / 64, by
    change i.val / 64 < 32
    have hi : i.val < 2030 := i.isLt
    omega⟩
  have hi : i.val % 64 < (edgeData b).length := by
    rw [edgeData_length]
    change i.val % 64 < min 64 (2030 - 64 * (i.val / 64))
    have hi : i.val < 2030 := i.isLt
    omega
  have hi' : i.val % 64 < ((edgeData b).zipIdx (64 * b.val)).length := by
    simpa only [List.length_zipIdx] using hi
  have hc := List.all_eq_true.mp (edges_checked b) _ (List.getElem_mem hi')
  have he : 64 * b.val + i.val % 64 = i.val := by dsimp only [b]; omega
  simp only [List.getElem_zipIdx, he, Bool.and_eq_true, beq_iff_eq] at hc
  change rowProduct (edgeAt i.val).2.1 (rows (edgeAt i.val).1) 52 = (edgeAt i.val).2.2
  rw [hc.1]
  exact hc.2

private def checkPaths (b : Fin pathBatchCount) : Bool :=
  ((pathData b).toList.zipIdx (64 * b.val)).all (fun p =>
    checkPath edges (letters p.2 ++ letters p.2) p.1.1 p.1.1 p.1.2)

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_00 : checkPaths 0 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_01 : checkPaths 1 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_02 : checkPaths 2 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_03 : checkPaths 3 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_04 : checkPaths 4 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_05 : checkPaths 5 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_06 : checkPaths 6 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_07 : checkPaths 7 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_08 : checkPaths 8 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_09 : checkPaths 9 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_10 : checkPaths 10 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_11 : checkPaths 11 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_12 : checkPaths 12 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_13 : checkPaths 13 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_14 : checkPaths 14 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_15 : checkPaths 15 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_16 : checkPaths 16 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_17 : checkPaths 17 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_18 : checkPaths 18 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_19 : checkPaths 19 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_20 : checkPaths 20 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_21 : checkPaths 21 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_22 : checkPaths 22 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_23 : checkPaths 23 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_24 : checkPaths 24 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_25 : checkPaths 25 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_26 : checkPaths 26 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_27 : checkPaths 27 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_28 : checkPaths 28 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_29 : checkPaths 29 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_30 : checkPaths 30 = true := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 10000 in
private theorem path_check_31 : checkPaths 31 = true := by decide +kernel

private theorem paths_checked (b : Fin pathBatchCount) : checkPaths b = true := by
  fin_cases b
  · exact path_check_00
  · exact path_check_01
  · exact path_check_02
  · exact path_check_03
  · exact path_check_04
  · exact path_check_05
  · exact path_check_06
  · exact path_check_07
  · exact path_check_08
  · exact path_check_09
  · exact path_check_10
  · exact path_check_11
  · exact path_check_12
  · exact path_check_13
  · exact path_check_14
  · exact path_check_15
  · exact path_check_16
  · exact path_check_17
  · exact path_check_18
  · exact path_check_19
  · exact path_check_20
  · exact path_check_21
  · exact path_check_22
  · exact path_check_23
  · exact path_check_24
  · exact path_check_25
  · exact path_check_26
  · exact path_check_27
  · exact path_check_28
  · exact path_check_29
  · exact path_check_30
  · exact path_check_31

private theorem pathData_size (b : Fin pathBatchCount) : (pathData b).size = 64 := by
  fin_cases b
  all_goals rfl

private theorem path_checked (n : Fin 2048) :
    ∃ a is, checkPath edges (letters n.val ++ letters n.val) a a is = true := by
  let b : Fin pathBatchCount := ⟨n.val / 64, by
    change n.val / 64 < 32
    omega⟩
  have hn : n.val % 64 < (pathData b).size := by rw [pathData_size]; omega
  have hi : n.val % 64 < ((pathData b).toList.zipIdx (64 * b.val)).length := by
    simpa only [List.length_zipIdx, Array.length_toList] using hn
  have ha := List.all_eq_true.mp (paths_checked b) _ (List.getElem_mem hi)
  have he : 64 * b.val + n.val % 64 = n.val := by dsimp only [b]; omega
  simp only [List.getElem_zipIdx, Array.getElem_toList, he] at ha
  exact ⟨_, _, ha⟩

/-- Every one of the 2,048 binary outer words has nonidentity square. -/
public theorem binaryWord_square_ne_one (n : Fin 2048) :
    (binaryWord n.val)^2 ≠ 1 := by
  intro h
  obtain ⟨a, is, hc⟩ := path_checked n
  apply checkPath_sound edges edges_valid _ _ _ _ hc
  apply mod_eq_of_bits_eq
  rw [List.map_append, bits_fold, List.map_append, List.prod_append,
    letters_prod, ← pow_two, ← Units.val_pow_eq_pow_val, h, Units.val_one,
    Matrix.vecMul_one]

end Tits.InvolutionRootGeometry.BinaryDerivedFusion.OuterSquares
