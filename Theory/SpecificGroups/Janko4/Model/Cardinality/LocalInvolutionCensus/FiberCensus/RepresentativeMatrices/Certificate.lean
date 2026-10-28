module

public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.Packed
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Packed certificates for displacement rank

Two checked binary row expansions identify a matrix's row span with that of
an explicit basis. An identity pivot minor proves independence of the basis.
The resulting equality concerns mathematical `Matrix.rank`; no elimination
algorithm or external evaluation is trusted. This is the finite linear algebra
used for the max2 representatives (Aschbacher--Smith, refs/quasithin.pdf,
printed pp.64--65, A.6.1--4). The packed row convention and ATLAS attribution
are documented in Janko4.Model.Data.
-/

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices
open Janko4.GeneratorCertificates

def decode {m n : ℕ} (rows : Fin m → ℕ) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => bit (rows i) j.val

def combine {m : ℕ} (rows : Fin m → ℕ) (x : ℕ) : ℕ :=
  xorList (List.ofFn (fun k : Fin m => if x.testBit k.val then rows k else 0))

theorem decode_combine {m n p : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ) :
    (decode (fun i => combine b (a i)) : Matrix (Fin m) (Fin p) (ZMod 2)) =
      decode a * decode b := by
  funext i j
  simp only [decode, combine, bit_xorList, List.map_ofFn, List.sum_ofFn, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [bit]
  cases h : (a i).testBit k.val <;> simp [h]

theorem rank_certificate {r : ℕ} (rows : Vector ℕ 112) (basis : Fin r → ℕ)
    (fromRows : Fin r → ℕ) (fromBasis : Fin 112 → ℕ) (pivots : Fin r → Fin 112)
    (he : ∀ i, combine rows.get (fromRows i) = basis i)
    (hm : ∀ i, combine basis (fromBasis i) = rows.get i)
    (hp : ∀ i j, bit (basis i) (pivots j).val = if i = j then 1 else 0) :
    (decodeRows rows).rank = r := by
  let E : Matrix (Fin r) (Fin 112) (ZMod 2) := decode basis
  have he' : E = decode fromRows * decodeRows rows := by
    change decode basis = decode fromRows * decode rows.get
    rw [← decode_combine]
    exact congrArg decode (funext fun i => (he i).symm)
  have hm' : decodeRows rows = decode fromBasis * E := by
    change decode rows.get = decode fromBasis * decode basis
    rw [← decode_combine]
    exact congrArg decode (funext fun i => (hm i).symm)
  have hp' : E.submatrix id pivots = 1 := by
    funext i j
    exact (hp i j).trans (Matrix.one_apply (i := i) (j := j)).symm
  have hr : E.rank = r := by
    apply le_antisymm (by simpa using Matrix.rank_le_card_height E)
    calc
      r = (1 : Matrix (Fin r) (Fin r) (ZMod 2)).rank := by simp
      _ = (E.submatrix id pivots).rank := by rw [hp']
      _ ≤ E.rank := Matrix.rank_submatrix_le _ _ _
  apply le_antisymm
  · calc
      (decodeRows rows).rank = (decode fromBasis * E).rank := by rw [hm']
      _ ≤ E.rank := Matrix.rank_mul_le_right _ _
      _ = r := hr
  · calc
      r = E.rank := hr.symm
      _ = (decode fromRows * decodeRows rows).rank := by rw [he']
      _ ≤ (decodeRows rows).rank := Matrix.rank_mul_le_right _ _
def displacement (rows : Vector ℕ 112) : Vector ℕ 112 :=
  Vector.ofFn (fun i => rows.get i ^^^ 2^i.val)

theorem decode_displacement (rows : Vector ℕ 112) :
    decodeRows (displacement rows) = decodeRows rows - 1 := by
  funext i j
  change bit ((displacement rows).get i) j.val = _
  rw [displacement, get_ofFn, bit_xor]
  have h : bit (2^i.val) j.val = (1 : BinaryMatrix) i j := by
    simpa only [packedOne, decodeRows, get_ofFn] using congrFun (congrFun decode_packedOne i) j
  rw [h]
  change decodeRows rows i j + (1 : BinaryMatrix) i j =
    decodeRows rows i j - (1 : BinaryMatrix) i j
  have hn : ∀ x : ZMod 2, -x = x := by decide +kernel
  simp only [sub_eq_add_neg, hn]

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices
