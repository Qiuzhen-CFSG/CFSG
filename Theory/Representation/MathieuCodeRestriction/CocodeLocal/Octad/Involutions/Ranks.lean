module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions.Coordinates
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions.Representatives

/-!
# The two native involution displacement ranks

For each representative, compute its displacement on the actual cocode
coordinates. A factorization through four or five coordinates gives an upper
bound, and a certified left inverse on selected columns gives the matching
lower bound. Every matrix identity is checked by the Lean kernel.

Source: Aschbacher–Smith H.14.4(3), printed pp.397–399. These are representative
calculations; arbitrary involutions require a native conjugacy witness.
-/

@[expose] public section

open Sporadic.Mathieu Representation.BinaryOffender
open scoped BigOperators
namespace MathieuCode.CocodeOctad.Involutions
noncomputable section

private lemma rank_certificate {n : ℕ}
    (M : Matrix (Fin 11) (Fin 11) (ZMod 2))
    (I : Matrix (Fin 11) (Fin n) (ZMod 2))
    (Q : Matrix (Fin n) (Fin 11) (ZMod 2))
    (L : Matrix (Fin n) (Fin 11) (ZMod 2))
    (J : Matrix (Fin 11) (Fin n) (ZMod 2))
    (hfactor : M = I * Q) (hminor : L * M * J = 1) : M.rank = n := by
  apply le_antisymm
  · calc
      M.rank = (I * Q).rank := congrArg Matrix.rank hfactor
      _ ≤ I.rank := Matrix.rank_mul_le_left _ _
      _ ≤ n := Matrix.rank_le_width _
  · have h := (Matrix.rank_mul_le_left (L * M) J).trans (Matrix.rank_mul_le_right L M)
    simpa only [hminor, Matrix.rank_one, Fintype.card_fin] using h

private def bitColumns {m n : ℕ} (v : Fin n → BitVec m) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => if (v j).getLsb i then 1 else 0

private def zMatrix : Matrix (Fin 11) (Fin 11) (ZMod 2) :=
  bitColumns ![396,664,201,325,989,461,396,325,201,989,593]

private def tMatrix : Matrix (Fin 11) (Fin 11) (ZMod 2) :=
  bitColumns ![1153,1538,1044,1477,1044,465,570,1153,1582,1538,0]

set_option maxRecDepth 4096 in
private lemma displacementMatrix_z : displacementMatrix z = zMatrix := by decide +kernel
set_option maxRecDepth 4096 in
private lemma displacementMatrix_t : displacementMatrix t = tMatrix := by decide +kernel

private def zImage : Matrix (Fin 11) (Fin 4) (ZMod 2) := bitColumns ![396,664,201,461]
private def zFactor : Matrix (Fin 4) (Fin 11) (ZMod 2) := bitColumns ![1,2,4,5,7,8,1,5,4,7,6]
private def zLeft : Matrix (Fin 4) (Fin 11) (ZMod 2) :=
  (bitColumns ![25,16,28,29]).transpose
private def zRight : Matrix (Fin 11) (Fin 4) (ZMod 2) := bitColumns ![1,2,4,32]

private def tImage : Matrix (Fin 11) (Fin 5) (ZMod 2) := bitColumns ![1153,1538,1044,1477,570]
private def tFactor : Matrix (Fin 5) (Fin 11) (ZMod 2) := bitColumns ![1,2,4,8,4,12,16,1,20,2,0]
private def tLeft : Matrix (Fin 5) (Fin 11) (ZMod 2) :=
  (bitColumns ![29,10,24,28,8]).transpose
private def tRight : Matrix (Fin 11) (Fin 5) (ZMod 2) := bitColumns ![1,2,4,8,64]

set_option maxRecDepth 4096 in
private lemma zMatrix_rank : zMatrix.rank = 4 := by
  exact rank_certificate zMatrix zImage zFactor zLeft zRight (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 4096 in
private lemma tMatrix_rank : tMatrix.rank = 5 := by
  exact rank_certificate tMatrix tImage tFactor tLeft tRight (by decide +kernel) (by decide +kernel)

lemma fixedCodim_z : fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4 := by
  rw [fixedCodim_eq_matrix_rank, displacementMatrix_z, zMatrix_rank]
lemma fixedCodim_t : fixedCodim cocodeRepresentation (Subgroup.zpowers t) = 5 := by
  rw [fixedCodim_eq_matrix_rank, displacementMatrix_t, tMatrix_rank]

end
end MathieuCode.CocodeOctad.Involutions
