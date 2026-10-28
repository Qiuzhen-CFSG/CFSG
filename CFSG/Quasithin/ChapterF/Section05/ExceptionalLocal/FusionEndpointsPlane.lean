module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionGraphPointCard
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical.Levi
/-!
# The binary plane endpoint fixed group

The restriction to the distinguished plane has fixed-field image of order at
most six and a symmetric-matrix kernel of order at most eight. A faithful
binary representation of C₂ × S₄ attains this bound. This identifies the
literal graph-fixed plane group used in Aschbacher--Smith F.5.3, p.300.
-/
noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Matrix Subgroup
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "J" => form F σ hσ
local notation "K" => FixedBy.subfield F σ
local notation "P" => planeParabolicSU F J
local notation "L" => localFactor F J

@[expose] public def graphFixedPlane : Subgroup P :=
  ((UnitaryFourOuter.matrixHom F σ hσ).comp (P).subtype).eqLocus (P).subtype

private def fixedRestrictionMatrix (a : graphFixedPlane) : Matrix (Fin 2) (Fin 2) K :=
  fun i j => ⟨restrictionMatrix F J a.val i j, by
    have h := a.property
    change UnitaryFourOuter.matrixHom F σ hσ a.val.val = a.val.val at h
    fin_cases i <;> fin_cases j
    all_goals exact congrArg (fun x : SU F J => x.val.val _ _) h⟩
private theorem fixedRestriction_det (a : graphFixedPlane) : (fixedRestrictionMatrix a).det = 1 := by
  have hne : (fixedRestrictionMatrix a).det ≠ 0 := by
    intro he
    have hh := congrArg Subtype.val he
    have hd : (restrictionMatrix F J a.val).det = 0 := by
      change (fixedRestrictionMatrix a).det.val = 0 at hh
      rw [Matrix.det_fin_two] at hh
      rw [Matrix.det_fin_two]
      exact hh
    exact (restriction F J a.val).det_ne_zero hd
  have hc : Nat.card K = 2 := PointLocal.fixedField_card 1 hn
  exact ((Nat.card_eq_two_iff' (0 : K)).mp hc).unique hne one_ne_zero

private def graphFixedPlaneRestriction : graphFixedPlane →* SpecialLinearGroup (Fin 2) K where
  toFun a := ⟨fixedRestrictionMatrix a, fixedRestriction_det a⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    change restrictionMatrix F J 1 i j = ((1 : Matrix (Fin 2) (Fin 2) K) i j).val
    rw [restrictionMatrix_one]
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  map_mul' a b := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    exact congrFun (congrFun (restrictionMatrix_mul F J a.val b.val) i) j

private def restrictionKernelRadical (a : graphFixedPlaneRestriction.ker) : radical F σ hσ := by
  let x : L := ⟨a.val.val.val, (mem_localFactor F J _).mpr ⟨a.val.val.property, ?_⟩⟩
  · refine ⟨x, (mem_radical F σ hσ x).mpr ?_⟩
    have he := congrArg (fun B : SpecialLinearGroup (Fin 2) K => B.val) a.property
    exact ⟨congrArg (fun B => (B 0 0).val) he, congrArg (fun B => (B 0 1).val) he,
      congrArg (fun B => (B 1 0).val) he, congrArg (fun B => (B 1 1).val) he⟩
  · have he := congrArg Subtype.val (fixedRestriction_det a.val)
    rw [Matrix.det_fin_two] at he ⊢
    exact he

private theorem kernel_parameter_fixed (a : graphFixedPlaneRestriction.ker) :
    ∀ i j, σ ((coordinatesOfRadical F σ hσ (restrictionKernelRadical a)).val i j) =
      (coordinatesOfRadical F σ hσ (restrictionKernelRadical a)).val i j := by
  intro i j
  have h := a.val.property
  change UnitaryFourOuter.matrixHom F σ hσ a.val.val.val = a.val.val.val at h
  fin_cases i <;> fin_cases j
  · exact congrArg (fun x : SU F J => x.val.val 0 3) h
  · exact congrArg (fun x : SU F J => x.val.val 0 2) h
  · exact congrArg (fun x : SU F J => x.val.val 1 3) h
  · exact congrArg (fun x : SU F J => x.val.val 1 2) h

private def kernelCoordinates (a : graphFixedPlaneRestriction.ker) : K × K × K :=
  (⟨(coordinatesOfRadical F σ hσ (restrictionKernelRadical a)).val 0 0, kernel_parameter_fixed a 0 0⟩,
   ⟨(coordinatesOfRadical F σ hσ (restrictionKernelRadical a)).val 0 1, kernel_parameter_fixed a 0 1⟩,
   ⟨(coordinatesOfRadical F σ hσ (restrictionKernelRadical a)).val 1 1, kernel_parameter_fixed a 1 1⟩)
private theorem kernelCoordinates_injective : Function.Injective kernelCoordinates := by
  intro a b he
  have h00 := congrArg (fun x : K × K × K => x.1.val) he
  have h01 := congrArg (fun x : K × K × K => x.2.1.val) he
  have h11 := congrArg (fun x : K × K × K => x.2.2.val) he
  have hx : coordinatesOfRadical F σ hσ (restrictionKernelRadical a) =
      coordinatesOfRadical F σ hσ (restrictionKernelRadical b) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · have ha := congrFun (congrFun (coordinatesOfRadical F σ hσ (restrictionKernelRadical a)).property 1) 0
      have hb := congrFun (congrFun (coordinatesOfRadical F σ hσ (restrictionKernelRadical b)).property 1) 0
      change σ _ = _ at ha hb
      exact ha.symm.trans ((congrArg σ h01).trans hb)
    · exact h11
  have hr : restrictionKernelRadical a = restrictionKernelRadical b := by
    rw [← unipotent_coordinatesOfRadical F σ hσ (restrictionKernelRadical a),
      ← unipotent_coordinatesOfRadical F σ hσ (restrictionKernelRadical b), hx]
  exact Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun r : radical F σ hσ => r.val.val) hr)))

public theorem graphFixedPlane_card_le : Nat.card graphFixedPlane ≤ 48 := by
  have hk : Nat.card graphFixedPlaneRestriction.ker ≤ 8 := by
    have hh := Nat.card_le_card_of_injective _ kernelCoordinates_injective
    have hc : Nat.card K = 2 := PointLocal.fixedField_card 1 hn
    simpa only [Nat.card_prod, hc] using hh
  have hr : Nat.card graphFixedPlaneRestriction.range ≤ 6 := by
    have hh := Nat.card_le_card_of_injective _ graphFixedPlaneRestriction.range.subtype_injective
    rw [Atlas.card_sl_two] at hh
    have hc : Nat.card K = 2 := PointLocal.fixedField_card 1 hn
    norm_num only [hc] at hh
    exact hh
  have he := graphFixedPlaneRestriction.ker.card_mul_index
  rw [index_ker] at he
  rw [← he]
  exact Nat.mul_le_mul hk hr
end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal

section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.EndpointPlane
open Matrix
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
local notation "C2" => Multiplicative (ZMod 2)
local notation "S4" => Equiv.Perm (Fin 4)
local notation "Mat" => Matrix (Fin 4) (Fin 4) (ZMod 2)
private def affinePoint (i : Fin 4) : Fin 2 → ZMod 2 :=
  ![![0,0], ![1,0], ![0,1], ![1,1]] i
private def affineShift (p : S4) : Fin 2 → ZMod 2 := affinePoint (p 0)
private def affineLinear (p : S4) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  !![(affinePoint (p 1)) 0 + (affinePoint (p 0)) 0,
      (affinePoint (p 2)) 0 + (affinePoint (p 0)) 0;
     (affinePoint (p 1)) 1 + (affinePoint (p 0)) 1,
      (affinePoint (p 2)) 1 + (affinePoint (p 0)) 1]
private def radicalMatrix (b : ZMod 2) (v : Fin 2 → ZMod 2) : Mat :=
  !![1,0,b+v 0+v 1,v 0;0,1,v 1,b+v 0+v 1;0,0,1,0;0,0,0,1]
private def leviMatrix (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Mat :=
  !![A 0 0,A 0 1,0,0;A 1 0,A 1 1,0,0;0,0,A 0 0,A 0 1;0,0,A 1 0,A 1 1]
private def binaryMatrix (a : C2 × S4) : Mat :=
  radicalMatrix a.1.toAdd (affineShift a.2) * leviMatrix (affineLinear a.2)
private theorem affine_mul : ∀ p q : S4,
    affineLinear (p*q) = affineLinear p * affineLinear q ∧
    affineShift (p*q) = affineShift p + affineLinear p *ᵥ affineShift q := by decide +kernel
private theorem levi_mul (A B : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    leviMatrix (A*B) = leviMatrix A * leviMatrix B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
private theorem radical_add (a b : ZMod 2) (v w : Fin 2 → ZMod 2) :
    radicalMatrix (a+b) (v+w) = radicalMatrix a v * radicalMatrix b w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
private theorem conjugation : ∀ p : S4, ∀ b : ZMod 2, ∀ v : Fin 2 → ZMod 2,
    leviMatrix (affineLinear p) * radicalMatrix b v =
      radicalMatrix b (affineLinear p *ᵥ v) * leviMatrix (affineLinear p) := by decide +kernel
private def binaryHom : C2 × S4 →* Mat where
  toFun := binaryMatrix
  map_one' := by decide +kernel
  map_mul' a b := by
    change binaryMatrix (a*b) = binaryMatrix a * binaryMatrix b
    change radicalMatrix (a.1.toAdd+b.1.toAdd) (affineShift (a.2*b.2)) *
      leviMatrix (affineLinear (a.2*b.2)) = _
    rw [
      (affine_mul a.2 b.2).1, (affine_mul a.2 b.2).2, radical_add, levi_mul]
    change _ = (radicalMatrix a.1.toAdd (affineShift a.2) * leviMatrix (affineLinear a.2)) *
      (radicalMatrix b.1.toAdd (affineShift b.2) * leviMatrix (affineLinear b.2))
    simp only [← mul_assoc]
    rw [mul_assoc (radicalMatrix a.1.toAdd (affineShift a.2))
      (leviMatrix (affineLinear a.2)), conjugation]
    simp only [mul_assoc]
private theorem binary_valid : ∀ a : C2 × S4,
    (binaryMatrix a).transpose * gram (ZMod 2) * binaryMatrix a = gram (ZMod 2) ∧
    binaryMatrix a 2 0 = 0 ∧ binaryMatrix a 3 0 = 0 ∧
    binaryMatrix a 2 1 = 0 ∧ binaryMatrix a 3 1 = 0 := by decide +kernel
private theorem binary_det (a : C2 × S4) : (binaryMatrix a).det = 1 := by
  have hg : (gram (ZMod 2)).det = 1 := by decide +kernel
  have hd := congrArg Matrix.det (binary_valid a).1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hg, mul_one] at hd
  apply CharTwo.sq_injective
  simpa only [pow_two, one_mul] using hd
private theorem binary_kernel : ∀ a : C2 × S4, binaryMatrix a = 1 → a = 1 := by decide +kernel

noncomputable section
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourPlaneLocal
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
private def binaryCast : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
private def liftedMatrix (a : C2 × S4) : Matrix (Fin 4) (Fin 4) F :=
  (binaryMatrix a).map binaryCast
private theorem cast_fixed (x : ZMod 2) : σ (binaryCast x) = binaryCast x :=
  DFunLike.congr_fun (Subsingleton.elim ((σ).toRingHom.comp binaryCast) binaryCast) x
private theorem gram_cast : (gram (ZMod 2)).map binaryCast = gram F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram]
private theorem lifted_det (a : C2 × S4) : (liftedMatrix a).det = 1 := by
  change (binaryCast.mapMatrix (binaryMatrix a)).det = 1
  rw [← binaryCast.map_det, binary_det a, map_one]
private theorem lifted_unitary (a : C2 × S4) :
    (form F σ hσ).conjTranspose (liftedMatrix a) * gram F * liftedMatrix a = gram F := by
  have hf : (form F σ hσ).conjTranspose (liftedMatrix a) = (liftedMatrix a).transpose := by
    ext i j
    exact cast_fixed _
  rw [hf, liftedMatrix, ← Matrix.transpose_map, ← gram_cast,
    ← Matrix.map_mul, ← Matrix.map_mul, (binary_valid a).1]
private def planeSU (a : C2 × S4) : SU F (form F σ hσ) :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (liftedMatrix a)
    (by rw [lifted_det]; exact one_ne_zero),
    lifted_unitary a, Units.ext (lifted_det a)⟩
private theorem planeSU_local (a : C2 × S4) :
    planeSU a ∈ planeParabolicSU F (form F σ hσ) := by
  apply (mem_planeParabolicSU F _ _).mpr
  change binaryCast (binaryMatrix a 2 0) = 0 ∧
    binaryCast (binaryMatrix a 3 0) = 0 ∧
    binaryCast (binaryMatrix a 2 1) = 0 ∧
    binaryCast (binaryMatrix a 3 1) = 0
  rcases (binary_valid a).2 with ⟨h0,h1,h2,h3⟩
  simp only [h0,h1,h2,h3,map_zero,and_self]
private theorem planeSU_fixed (a : C2 × S4) :
    UnitaryFourOuter.matrixHom F σ hσ (planeSU a) = planeSU a := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact cast_fixed _
private def planeHom : C2 × S4 →* graphFixedPlane where
  toFun a := ⟨⟨planeSU a, planeSU_local a⟩, planeSU_fixed a⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change binaryCast.mapMatrix (binaryHom 1) = 1
    rw [map_one, map_one]
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change binaryCast.mapMatrix (binaryHom (a*b)) =
      binaryCast.mapMatrix (binaryHom a) * binaryCast.mapMatrix (binaryHom b)
    rw [map_mul, map_mul]
private theorem planeHom_injective : Function.Injective planeHom := by
  apply (injective_iff_map_eq_one planeHom).mpr
  intro a ha
  have hm : liftedMatrix a = 1 := congrArg (fun x : graphFixedPlane => x.val.val.val.val) ha
  apply binary_kernel a
  apply Matrix.map_injective binaryCast.injective
  change binaryCast.mapMatrix (binaryMatrix a) = binaryCast.mapMatrix 1
  rw [map_one]
  exact hm
private theorem planeHom_bijective : Function.Bijective planeHom := by
  apply planeHom_injective.bijective_of_nat_card_le
  calc
    Nat.card graphFixedPlane ≤ 48 := graphFixedPlane_card_le
    _ = Nat.card (C2 × S4) := by
      norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

public def graphFixedPlaneEquivProduct : graphFixedPlane ≃* C2 × S4 :=
  (MulEquiv.ofBijective planeHom planeHom_bijective).symm

private theorem binary_long_coordinate : ∀ a : C2 × S4,
    binaryMatrix a = !![1,0,0,1;0,1,0,0;0,0,1,0;0,0,0,1] → a.1 ≠ 1 := by
  decide +kernel

/-- The literal long-root transvection has nonidentity central coordinate. -/
public theorem graphFixedPlaneEquivProduct_long_coordinate (x : graphFixedPlane)
    (hx : x.val.val.val.val = !![1,0,0,1;0,1,0,0;0,0,1,0;0,0,0,1]) :
    (graphFixedPlaneEquivProduct x).1 ≠ 1 := by
  obtain ⟨a,rfl⟩ := planeHom_bijective.2 x
  change ((MulEquiv.ofBijective planeHom planeHom_bijective).symm
    ((MulEquiv.ofBijective planeHom planeHom_bijective) a)).1 ≠ 1
  rw [MulEquiv.symm_apply_apply]
  apply binary_long_coordinate a
  apply Matrix.map_injective binaryCast.injective
  change liftedMatrix a = (
    !![1,0,0,1;0,1,0,0;0,0,1,0;0,0,0,1] : Mat).map binaryCast
  rw [show liftedMatrix a = !![1,0,0,1;0,1,0,0;0,0,1,0;0,0,0,1] from hx]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The two canonical Klein-four generators retain their literal binary matrices. -/
public theorem graphFixedPlaneEquivProduct_symm_klein_matrices :
    ((graphFixedPlaneEquivProduct.symm
      (1,Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3)).val.val.val.val = !![1,0,1,1;0,1,0,1;0,0,1,0;0,0,0,1]) ∧
    ((graphFixedPlaneEquivProduct.symm
      (1,Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3)).val.val.val.val = !![1,0,1,0;0,1,1,1;0,0,1,0;0,0,0,1]) := by
  have h1 : binaryMatrix (1,Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) = !![1,0,1,1;0,1,0,1;0,0,1,0;0,0,0,1] := by decide +kernel
  have h2 : binaryMatrix (1,Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3) = !![1,0,1,0;0,1,1,1;0,0,1,0;0,0,0,1] := by decide +kernel
  constructor
  · change (binaryMatrix (1,Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3)).map binaryCast = _
    rw [h1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · change (binaryMatrix (1,Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3)).map binaryCast = _
    rw [h2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

end
end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.EndpointPlane
