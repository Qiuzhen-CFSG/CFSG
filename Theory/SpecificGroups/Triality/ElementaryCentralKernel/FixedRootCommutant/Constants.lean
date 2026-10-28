module
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRootCommutant.BinaryConstants

/-! Transport the checked binary fixed-root matrices to arbitrary coefficient
rings of characteristic two, using the canonical ring homomorphism. -/

public section
namespace Triality.Standard.ElementaryCentralKernel.FixedRootCommutant

lemma rootMatrix_map {F K : Type*} [CommRing F] [CommRing K] (f : F →+* K)
    (i : Fin 4) (s : Bool) (t : F) :
    (rootMatrix i s t).map f = rootMatrix i s (f t) := by
  ext r c
  simp only [Matrix.map_apply, rootMatrix]
  split_ifs <;> simp

lemma supportMatrix_map {F K : Type*} [NonAssocSemiring F] [NonAssocSemiring K]
    (f : F →+* K) (l : List (Fin 28 × Fin 28)) :
    (supportMatrix l).map f = supportMatrix (F := K) l := by
  ext r c
  simp [supportMatrix]

variable {F : Type*} [CommRing F] [CharP F 2]

lemma central_constant (s : Bool) :
    rootMatrix (F := F) 1 s 1 = constantMatrix (if s then 0 else 1) := by
  have h := congrArg (fun M => M.map (ZMod.castHom (dvd_refl 2) F))
    (root_constant_binary s)
  simpa only [rootMatrix_map, map_one, constantMatrix, supportMatrix_map] using h

lemma folded_constant (s : Bool) :
    rootMatrix (F := F) 0 s 1 * rootMatrix 2 s 1 * rootMatrix 3 s 1 =
      constantMatrix (if s then 2 else 3) := by
  have h := congrArg (fun M => M.map (ZMod.castHom (dvd_refl 2) F))
    ((congrArg (fun M => M * rootMatrix 3 s 1) (arm_pair_binary s)).trans
      (arm_triple_binary s))
  simpa only [RingHom.mapMatrix_apply, Matrix.map_mul, rootMatrix_map, map_one,
    constantMatrix, supportMatrix_map] using h

end Triality.Standard.ElementaryCentralKernel.FixedRootCommutant
