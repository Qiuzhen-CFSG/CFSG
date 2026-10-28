module

public import Theory.SpecificGroups.SU3.OddRootFixers.NormalForms
public import Theory.SpecificGroups.SU3.ProjectiveGraphFixed
public import Theory.SpecificGroups.SU3.NormalizedRootCentralizers
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
import all Theory.SpecificGroups.SU3.ProjectiveGraphFixed

/-!
# The marked fixed-field block subgroup

The graph-fixed subgroup is an actual fixed-field SL₂ block, and hence PSL₂
in characteristic two. It contains the whole center of the upper root group.
Every diagonal unitary matrix with equal outer entries commutes with the
block. Projectivization preserves both this containment and pointwise
fixation; the existing graph-fixed equivalence retains its scalar-kernel proof.

The internal import is intentional: this extension supplies an equation for
the inverse of the existing opaque block equivalence, without changing the
widely imported implementation module. All other consumers use public APIs.
The equation follows the same calculation as `UnitaryStandardRoots`'s
`FixedCoordinates` extension, at the intrinsic group layer.

Source: GLS4, Chapter 4, Lemma 3.6(d); the block construction and scalar-kernel
calculation are in `ProjectiveGraphFixed`. Coefficient transport uses the
licensed ATLAS `fieldEquivPSL` API (`LICENSES/ATLAS.txt`).
-/

public section
open Matrix Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
open BorelTorus BorelTorus.EvenCenterAction
variable {E : Type*} [Field E] [CharP E 2] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

/-- The inverse graph-fixed equivalence is the literal fixed-field corner block. -/
theorem fixedBlock_val (A : SpecialLinearGroup (Fin 2) (FixedBy.subfield E J.conj)) :
    ((specialGraphFixedEquivSL2 J hJ).symm A).val.val.val =
      !![(A 0 0 : E),0,(A 0 1 : E);0,1,0;(A 1 0 : E),0,(A 1 1 : E)] := by
  rfl

/-- Every graph-fixed special matrix commutes with the specified diagonal actor. -/
theorem diagonal_commutes_fixed (d : J.unitarySubgroup) (hd : IsRootDiagonal J d)
    (x : (specialGraphAut J hJ).fixedSubgroup) : d.val * x.val.val = x.val.val * d.val := by
  obtain ⟨A, rfl⟩ := (specialGraphFixedEquivSL2 J hJ).symm.surjective x
  apply Units.ext
  change d.val.val * _ = _ * d.val.val
  rw [fixedBlock_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hd.1, hd.2, mul_comm]

/-- A diagonal root actor fixes the entire special graph-fixed subgroup. -/
theorem diagonal_fixes_special (d : J.unitarySubgroup) (hd : IsRootDiagonal J d)
    (a : MulAut J.specialSubgroup)
    (ha : ∀ x : J.specialSubgroup, (a x).val = d.val * x.val * d.val⁻¹) :
    ∀ x ∈ (specialGraphAut J hJ).fixedSubgroup, a x = x := by
  intro x hx
  apply Subtype.ext
  rw [ha, diagonal_commutes_fixed J hJ d hd ⟨x, hx⟩, mul_assoc, mul_inv_cancel, mul_one]

/-- The literal projective diagonal actor fixes the projective graph-fixed subgroup. -/
theorem diagonal_fixes_projective (d : J.unitarySubgroup) (hd : IsRootDiagonal J d) :
    ∀ x ∈ (projectiveGraphAut J hJ).fixedSubgroup, J.unitaryConj d x = x := by
  intro x hx
  obtain ⟨y, hy⟩ := projectiveGraphAut_fixed_representative J hJ ⟨x, hx⟩
  change J.specialToProjective y.val = x at hy
  rw [← hy, unitaryConj_specialToProjective]
  congr 1
  apply Subtype.ext
  rw [specialUnitaryConj_val, diagonal_commutes_fixed J hJ d hd y,
    mul_assoc, mul_inv_cancel, mul_one]

omit [CharP E 2] in
private theorem rootSU_injective : Function.Injective (hermitianUnipotentSU J hJ) := by
  intro z w h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun x : J.specialSubgroup => x.val.val 0 1) h)
    (congrArg (fun x : J.specialSubgroup => x.val.val 0 2) h)

private theorem special_central_fixed (b : Multiplicative (fixedField J)) :
    hermitianUnipotentSU J hJ (centralCoord J b) ∈ (specialGraphAut J hJ).fixedSubgroup := by
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  apply Subtype.ext
  apply Units.ext
  rw [specialGraphAut_apply_val]
  change (hermitianUnipotentMatrix J (centralCoord J b)).map J.conj =
    hermitianUnipotentMatrix J (centralCoord J b)
  have hz : (centralCoord J b).val.1 = 0 := rfl
  have hb : (centralCoord J b).val.2 = (b.toAdd : E) := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianUnipotentMatrix, hz, hb, fixedField_mem]

variable [Finite E] {n : ℕ} (hn : 2 ≤ n)
  (hcard : Nat.card E = (2 ^ n) ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)

include hn hcard hfixed in
/-- The whole embedded center of the actual special root group lies in the block. -/
theorem special_root_center_le_fixed :
    (center (specialRoot J hJ)).map (specialRoot J hJ).subtype ≤
      (specialGraphAut J hJ).fixedSubgroup := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, hz⟩ := x.property
  have hzc : z ∈ center (hermitianUnipotentCoord J) := by
    apply mem_center_iff.mpr
    intro w
    apply rootSU_injective J hJ
    rw [map_mul, map_mul, hz]
    exact congrArg Subtype.val (mem_center_iff.mp hx
      ⟨hermitianUnipotentSU J hJ w, ⟨w, rfl⟩⟩)
  rw [NormalizedRootCentralizers.coord_center J (by omega) hcard hfixed] at hzc
  obtain ⟨b, rfl⟩ := hzc
  change x.val ∈ _
  rw [← hz]
  exact special_central_fixed J hJ b

include hn hcard hfixed in
/-- The projective root center is contained with its literal embedding. -/
theorem projective_root_center_le_fixed :
    (center (projectiveRoot J hJ)).map (projectiveRoot J hJ).subtype ≤
      (projectiveGraphAut J hJ).fixedSubgroup := by
  rw [NormalizedRootCentralizers.root_center J (by omega) hcard hfixed hJ]
  rintro _ ⟨b, rfl⟩
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  have hp : centralMap J hJ b = J.specialToProjective
      (hermitianUnipotentSU J hJ (centralCoord J b)) := by
    apply Subtype.ext
    change (hermitianUnipotentPSU J hJ (centralCoord J b)).val = _
    rw [hermitianUnipotentPSU_val, specialToProjective_apply_val]
    rfl
  rw [hp, projectiveGraphAut_specialToProjective,
    (MulAut.mem_fixedSubgroup _ _).mp (special_central_fixed J hJ b)]

private noncomputable def fixedFieldEquivBinary :
    fixedField J ≃+* BenderSuzuki.PFAppendixIII.BinaryGaloisField n := by
  letI := ZMod.algebra (fixedField J) 2
  exact (GaloisField.algEquivGaloisField 2 n
    (show Nat.card (fixedField J) = 2 ^ n from hfixed)).toRingEquiv

/-- The actual special block, without quotienting its ambient group, is PSL₂(2ⁿ). -/
noncomputable def specialFixedEquivBinary :
    (specialGraphAut J hJ).fixedSubgroup ≃* PSL2BinaryMatrixGroup n :=
  (projectiveGraphFixedEquivSpecial J hJ).symm.trans
    ((projectiveGraphFixedEquiv J hJ).trans
      (Atlas.fieldEquivPSL 2 (fixedFieldEquivBinary J hfixed)))

/-- The actual projective block is PSL₂ over the binary field of the same exponent. -/
noncomputable def projectiveFixedEquivBinary :
    (projectiveGraphAut J hJ).fixedSubgroup ≃* PSL2BinaryMatrixGroup n :=
  (projectiveGraphFixedEquiv J hJ).trans
    (Atlas.fieldEquivPSL 2 (fixedFieldEquivBinary J hfixed))

end BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
