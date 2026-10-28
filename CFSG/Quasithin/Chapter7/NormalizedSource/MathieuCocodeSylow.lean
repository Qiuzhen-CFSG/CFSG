module
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.Native

/-!
# The fixed line in the M24 cocode branch

Ten displacement rows of two generators of the certified native Sylow
subgroup, together with coordinate ten, form an invertible binary matrix.
The two small matrix certificates are checked by the kernel. Thus evaluation
at that coordinate injects the native fixed space into F₂. Sylow conjugacy
transports the bound to every actual Sylow subgroup of M24.

NonFFSourceMathieuM24Block applies this to the original Sylow action,
proving the order-two assertion in source 8.2.10(4). The coordinates and
permutations are the existing native MathieuCode and M24LocalGeometry ones.
Source: Aschbacher–Smith H.15 and 8.2.10, printed pp.398–399,721,
refs/quasithin.pdf.
-/

public noncomputable section
open Sporadic.Mathieu Representation.BinaryOffender
open Sporadic.Mathieu.M24LocalGeometry
open MathieuCode MathieuCode.CocodeOctad.Involutions MathieuCode.QuadraticActors
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCocodeSylow

private def selectedRow : Fin 10 → Fin 4 × Fin 11 :=
  ![(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(1,0),(1,2),(1,5)]

private def testMatrix : Matrix (Fin 11) (Fin 11) (ZMod 2) := fun i j =>
  if h : i.val < 10 then
    let a := selectedRow ⟨i.val,h⟩
    pointMatrix (SylowNormalizer.generatorPoint a.1) a.2 j
  else if j = 10 then 1 else 0

private def matrixRow : Fin 11 → ℕ :=
  ![1916,1279,1338,651,115,1423,321,517,653,1879,1024]
private def inverseRow : Fin 11 → ℕ :=
  ![247,1178,1426,1108,685,568,1256,1492,1119,1509,1024]
private def encodedMatrix : Matrix (Fin 11) (Fin 11) (ZMod 2) :=
  fun i j => bit (matrixRow i) j.val
private def inverseMatrix : Matrix (Fin 11) (Fin 11) (ZMod 2) :=
  fun i j => bit (inverseRow i) j.val

private theorem matrix_check : testMatrix = encodedMatrix := by decide +kernel
private theorem inverse_check : inverseMatrix * encodedMatrix = 1 := by decide +kernel

private theorem coordinate_injective : Function.Injective
    (fun v : fixedSpace cocodeRepresentation SylowNormalizer.candidate => coordinates v.val 10) := by
  suffices hz : ∀ v : fixedSpace cocodeRepresentation SylowNormalizer.candidate,
      coordinates v.val 10 = 0 → v = 0 by
    intro x y he
    change coordinates x.val 10 = coordinates y.val 10 at he
    have hd : coordinates ((x-y).val) 10 = 0 := by
      change (coordinates (x.val-y.val)) 10 = 0
      rw [map_sub,Pi.sub_apply,he,sub_self]
    exact sub_eq_zero.mp (hz (x-y) hd)
  intro v hv
  have hd (a : Fin 4) : (pointMatrix (SylowNormalizer.generatorPoint a)).mulVecLin
      (coordinates v.val) = 0 := by
    have he : pointMatrix (SylowNormalizer.generatorPoint a) =
        displacementMatrix (SylowNormalizer.generator a) := by
      rw [displacementMatrix_point]
      congr 1
      funext x
      exact (SylowNormalizer.generatorPerm_apply a x).symm
    rw [he,displacementMatrix_eq]
    simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply]
    have hs : sectionMap (coordinates v.val) = v.val :=
      LinearMap.congr_fun sectionMap_coordinates v.val
    have hf : cocodeRepresentation (SylowNormalizer.generator a) v.val = v.val :=
      v.property ⟨SylowNormalizer.generator a,SylowNormalizer.generator_mem a⟩
    rw [hs,hf,sub_self,map_zero]
  have ht : testMatrix.mulVecLin (coordinates v.val) = 0 := by
    ext i
    by_cases hi : i.val < 10
    · have ha := congrFun (hd (selectedRow ⟨i.val,hi⟩).1) (selectedRow ⟨i.val,hi⟩).2
      simpa only [Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,testMatrix,hi,dif_pos,Pi.zero_apply] using ha
    · have hie : i = 10 := Fin.ext (by omega)
      subst i
      simpa [Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,testMatrix] using hv
  have he : coordinates v.val = 0 := by
    have hh := congrArg inverseMatrix.mulVecLin ht
    rw [matrix_check,←LinearMap.comp_apply,←Matrix.mulVecLin_mul,inverse_check,
      Matrix.mulVecLin_one,LinearMap.id_apply,map_zero] at hh
    exact hh
  apply Subtype.ext
  exact coordinateEquiv.injective (he.trans (map_zero coordinates).symm)

private theorem native_fixed_card_le_two :
    Nat.card (fixedSpace cocodeRepresentation SylowNormalizer.candidate) ≤ 2 := by
  simpa only [Nat.card_zmod] using Nat.card_le_card_of_injective _ coordinate_injective

/-- Every native M24 Sylow subgroup has at most two fixed cocode vectors. -/
theorem fixed_card_le_two (S : Sylow 2 M24) :
    Nat.card (fixedSpace cocodeRepresentation S) ≤ 2 := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 SextetCore.nativeSylow S
  have he : SylowNormalizer.candidate.map (MulAut.conj g).toMonoidHom =
      (S : Subgroup M24) := congrArg Sylow.toSubgroup hg
  have hc := Nat.card_congr
    (fixedSpaceConjEquiv cocodeRepresentation SylowNormalizer.candidate g).toEquiv
  rw [he] at hc
  exact hc.symm.le.trans native_fixed_card_le_two

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCocodeSylow
