module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Coordinates
public import Theory.Mathieu.M12.Properties.InvolutionFusion

/-!
# Inner involution displacements on the M₁₂ heart

The two marked involutions have displacement four. A factorization through
four coordinates proves the upper bound, and an invertible minor proves the
lower bound. Exhaustive inner involution fusion then covers every involution.
The same method gives displacement six for the marked element of cycle type
1³3³, witnessing sharpness of the odd-order lower bound once it is established.

Every finite identity is checked by Lean's kernel. The certificate generator
is in `Inner/source/generate.py`; its output is untrusted. The marked
permutations are those already certified in `M12.SmallParabolicPair.Seeds`.
Source: Aschbacher–Smith H.11.1(2) and the preceding discussion of β, printed
p.392, combined manuscript of 1 March 2004.
-/

public section
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations

private theorem rank_certificate {n : ℕ}
    (M : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (I : Matrix (Fin 10) (Fin n) (ZMod 2))
    (Q : Matrix (Fin n) (Fin 10) (ZMod 2))
    (L : Matrix (Fin n) (Fin 10) (ZMod 2))
    (J : Matrix (Fin 10) (Fin n) (ZMod 2))
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

private def zMatrix : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  bitColumns ![1023,989,1023,999,999,989,703,1023,703,1023]
private def zImage : Matrix (Fin 10) (Fin 4) (ZMod 2) := bitColumns ![1023,989,999,703]
private def zFactor : Matrix (Fin 4) (Fin 10) (ZMod 2) := bitColumns ![1,2,1,4,4,2,8,1,8,1]
private def zLeft : Matrix (Fin 4) (Fin 10) (ZMod 2) := (bitColumns ![74,3,9,65]).transpose
private def zRight : Matrix (Fin 10) (Fin 4) (ZMod 2) := bitColumns ![1,2,8,64]

set_option maxRecDepth 4096 in
private theorem displacementMatrix_z :
    displacementMatrix Sporadic.Mathieu.M12SmallPair.zPerm = zMatrix := by decide +kernel

set_option maxRecDepth 4096 in
private theorem zMatrix_rank : zMatrix.rank = 4 := by
  exact rank_certificate zMatrix zImage zFactor zLeft zRight (by decide +kernel) (by decide +kernel)

theorem fixedCodim_z :
    fixedCodim m12HeartRepresentation (Subgroup.zpowers Sporadic.Mathieu.M12SmallPair.z) = 4 := by
  rw [fixedCodim_eq_matrix_rank]
  change (displacementMatrix Sporadic.Mathieu.M12SmallPair.zPerm).rank = 4
  rw [displacementMatrix_z, zMatrix_rank]

private def thirdMatrix : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  bitColumns ![521,266,140,0,999,104,104,140,266,521]
private def thirdImage : Matrix (Fin 10) (Fin 4) (ZMod 2) := bitColumns ![521,266,140,999]
private def thirdFactor : Matrix (Fin 4) (Fin 10) (ZMod 2) := bitColumns ![1,2,4,0,8,15,15,4,2,1]
private def thirdLeft : Matrix (Fin 4) (Fin 10) (ZMod 2) := (bitColumns ![14,13,11,15]).transpose
private def thirdRight : Matrix (Fin 10) (Fin 4) (ZMod 2) := bitColumns ![1,2,4,16]

set_option maxRecDepth 4096 in
private theorem displacementMatrix_third :
    displacementMatrix Sporadic.Mathieu.M12SmallPair.thirdPerm = thirdMatrix := by decide +kernel

set_option maxRecDepth 4096 in
private theorem thirdMatrix_rank : thirdMatrix.rank = 4 := by
  exact rank_certificate thirdMatrix thirdImage thirdFactor thirdLeft thirdRight
    (by decide +kernel) (by decide +kernel)

theorem fixedCodim_third :
    fixedCodim m12HeartRepresentation (Subgroup.zpowers Sporadic.Mathieu.M12SmallPair.third) = 4 := by
  rw [fixedCodim_eq_matrix_rank]
  change (displacementMatrix Sporadic.Mathieu.M12SmallPair.thirdPerm).rank = 4
  rw [displacementMatrix_third, thirdMatrix_rank]

private def cubicMatrix : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  bitColumns ![16,16,532,280,64,16,80,148,751,656]
private def cubicImage : Matrix (Fin 10) (Fin 6) (ZMod 2) := bitColumns ![16,532,280,64,148,751]
private def cubicFactor : Matrix (Fin 6) (Fin 10) (ZMod 2) := bitColumns ![1,1,2,4,8,1,9,16,32,19]
private def cubicLeft : Matrix (Fin 6) (Fin 10) (ZMod 2) := (bitColumns ![28,132,9,65,129,1]).transpose
private def cubicRight : Matrix (Fin 10) (Fin 6) (ZMod 2) := bitColumns ![1,4,8,16,128,256]

set_option maxRecDepth 4096 in
private theorem displacementMatrix_cubic :
    displacementMatrix Sporadic.Mathieu.M12SmallPair.cubicActorPerm = cubicMatrix := by decide +kernel

set_option maxRecDepth 4096 in
private theorem cubicMatrix_rank : cubicMatrix.rank = 6 := by
  exact rank_certificate cubicMatrix cubicImage cubicFactor cubicLeft cubicRight
    (by decide +kernel) (by decide +kernel)

theorem fixedCodim_cubicActor :
    fixedCodim m12HeartRepresentation (Subgroup.zpowers Sporadic.Mathieu.M12SmallPair.cubicActor) = 6 := by
  rw [fixedCodim_eq_matrix_rank]
  change (displacementMatrix Sporadic.Mathieu.M12SmallPair.cubicActorPerm).rank = 6
  rw [displacementMatrix_cubic, cubicMatrix_rank]

theorem fixedCodim_involution (t : Sporadic.Mathieu.M12) (ht : orderOf t = 2) :
    fixedCodim m12HeartRepresentation (Subgroup.zpowers t) = 4 := by
  rcases Sporadic.Mathieu.M12InvolutionFusion.marked_fusion t ht with h | h
  · obtain ⟨g, rfl⟩ := isConj_iff.mp h
    rw [fixedCodim_zpowers_conj, fixedCodim_z]
  · obtain ⟨g, rfl⟩ := isConj_iff.mp h
    rw [fixedCodim_zpowers_conj, fixedCodim_third]

theorem finrank_fixedSpace_involution (t : Sporadic.Mathieu.M12) (ht : orderOf t = 2) :
    Module.finrank (ZMod 2) (fixedSpace m12HeartRepresentation (Subgroup.zpowers t)) = 6 := by
  have hd := fixedCodim_add_finrank m12HeartRepresentation (Subgroup.zpowers t)
  rw [fixedCodim_involution t ht, finrank_m12Heart] at hd
  omega

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations
