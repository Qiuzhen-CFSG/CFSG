module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.Data
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.Rows

/-!
# Packed forward and inverse-word rows

Right multiplication of a binary row is packed XOR. Iterating this operation
agrees with the first row of the corresponding matrix product. The forward
row starts with the certified kernel-word row and appends the source lift;
the proposed inverse row starts with the lift row and appends the selected
inverse factors in reverse order. Their comparison is a finite arithmetic
condition, without any assumption that first rows determine group elements.

The witnesses come from the ATLAS `J4G1-max2W1` program; see the attribution
and generator in `Coverage/source/README.md`. The source motivation is
Aschbacher--Smith, `refs/quasithin.pdf`, printed pp.64--65, A.6.1--4.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation
open Janko4.GeneratorCertificates

def unpackRow (r : ℕ) : Fin 112 → ZMod 2 := fun i => bit r i.val

def rowWord : List (Vector ℕ 112) → ℕ → ℕ
  | [], r => r
  | a :: as, r => rowWord as (packedRow r a)

def inverseFactors (m : Fin 8192) : List (Vector ℕ 112) :=
  (List.ofFn (fun i : Fin 13 =>
    if m.val.testBit i.val then inverseFactorRows i else packedOne)).reverse

def forwardRow (j : Fin 4) (m : Fin 8192) : ℕ :=
  packedRow (KernelSeparation.row m.val) (liftRows j)

def backwardRow (j : Fin 4) (m : Fin 8192) : ℕ :=
  rowWord (inverseFactors m) ((liftRows j).get 0)

def RowsAgree (j : Fin 4) (m : Fin 8192) : Prop :=
  unpackRow (forwardRow j m) = unpackRow (backwardRow j m)

theorem unpack_packedRow (r : ℕ) (a : Vector ℕ 112) :
    unpackRow (packedRow r a) = unpackRow r ᵥ* decodeRows a := by
  funext j
  change bit (packedRow r a) j.val = _
  rw [packedRow, bit_xorList, List.map_ofFn, List.sum_ofFn]
  rw [Matrix.vecMul_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [unpackRow, decodeRows, bit]
  cases h : r.testBit k.val <;> simp [h]

theorem unpack_rowWord (as : List (Vector ℕ 112)) (r : ℕ) :
    unpackRow (rowWord as r) = unpackRow r ᵥ* (as.map decodeRows).prod := by
  induction as generalizing r with
  | nil => simp only [rowWord, List.map_nil, List.prod_nil, Matrix.vecMul_one]
  | cons a as ih =>
    rw [rowWord, ih, unpack_packedRow, Matrix.vecMul_vecMul,
      List.map_cons, List.prod_cons]


end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage
