module

public import BenderSuzuki.MatrixGroups.Unitary
public import Theory.SpecificGroups.GL2.DiagonalSwap
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Group

/-!
# Quaternion rotation in a hyperbolic unitary plane

Let the Hermitian involution negate a unit r and fix a square root i of -1.
The diagonal torus element a = diag(r,-r⁻¹), the coordinate swap b, and
j = diag(i,-i), k = abj satisfy the quaternion relations. The matrix
(I+j+k+jk)/2 is a determinant-one isometry and intertwines j with k.
Its field coboundary is exactly ab. Consequently, in every homomorphic
image carrying the given field action c, this rotation conjugates c to abc;
that element inverts the image of a. The homomorphism need not be injective,
so these identities also apply after projective descent.

Application: the exceptional outer involution in Aschbacher--Smith E.1.14(7),
printed p.214, citing Aschbacher (1982), Lemma 4.11. The ambient identification
of the marked cyclic core is separate from these explicit matrix identities.
-/

public section
open Matrix BenderSuzuki.MatrixGroups
open scoped Matrix
namespace Matrix.UnitaryQuaternionRotation
variable {F : Type*} [Field F]

@[expose] def rotationMatrix (r : Fˣ) (i : F) : Matrix (Fin 2) (Fin 2) F :=
  !![(1+i)/2, (r:F)*(1-i)/2; -((r:F)⁻¹)*(1+i)/2, (1-i)/2]

theorem rotation_det (r : Fˣ) (i : F) (hi : i^2 = -1) (h2 : (2:F) ≠ 0) :
    (rotationMatrix r i).det = 1 := by
  simp [rotationMatrix, det_fin_two]
  field_simp
  ring_nf
  simp [hi]
  ring

theorem rotation_unitary (J : HermitianForm 2 F)
    (hJ : J.form = !![0,1;1,0]) (r : Fˣ) (i : F)
    (hr : J.conj (r:F) = -(r:F)) (hfix : J.conj i = i)
    (hi : i^2 = -1) (h2 : (2:F) ≠ 0) :
    J.conjTranspose (rotationMatrix r i) * J.form * rotationMatrix r i = J.form := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rotationMatrix, HermitianForm.conjTranspose, hJ, mul_apply, Fin.sum_univ_two,
      map_div₀, map_ofNat, hr, hfix] <;>
    field_simp <;> ring_nf <;> simp [hi] <;> ring

@[expose] def torusGL (r : Fˣ) : GL (Fin 2) F :=
  GeneralLinearGroup.diagonalPair F (r, -r⁻¹)

theorem torus_unitary (J : HermitianForm 2 F)
    (hJ : J.form = !![0,1;1,0]) (r : Fˣ)
    (hr : J.conj (r:F) = -(r:F)) : torusGL r ∈ J.unitarySubgroup := by
  rw [J.mem_unitarySubgroup_iff]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [torusGL, GeneralLinearGroup.diagonalPair, HermitianForm.conjTranspose,
      hJ, mul_apply, Fin.sum_univ_two, hr]

@[expose] def torus (J : HermitianForm 2 F) (hJ : J.form = !![0,1;1,0])
    (r : Fˣ) (hr : J.conj (r:F) = -(r:F)) : J.unitarySubgroup :=
  ⟨torusGL r, torus_unitary J hJ r hr⟩

@[expose] def swap (J : HermitianForm 2 F) (hJ : J.form = !![0,1;1,0]) :
    J.unitarySubgroup :=
  ⟨GeneralLinearGroup.coordinateSwap F, by
    rw [J.mem_unitarySubgroup_iff]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [GeneralLinearGroup.coordinateSwap, HermitianForm.conjTranspose,
        hJ, mul_apply, Fin.sum_univ_two]⟩

@[expose] def fieldConj (J : HermitianForm 2 F) (hJ : J.form = !![0,1;1,0]) :
    J.unitarySubgroup →* J.unitarySubgroup :=
  ((GeneralLinearGroup.map J.conj.toRingHom).comp J.unitarySubgroup.subtype).codRestrict
    J.unitarySubgroup (by
      intro u
      rw [J.mem_unitarySubgroup_iff]
      change J.conjTranspose (u.val.val.map J.conj) * J.form *
        (u.val.val.map J.conj) = J.form
      have hform : J.form.map J.conj = J.form := by
        rw [hJ]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A.map J.conj)
        ((J.mem_unitarySubgroup_iff u.val).mp u.property)
      have hadj : (J.conjTranspose u.val.val).map J.conj =
          J.conjTranspose (u.val.val.map J.conj) := by
        ext i j
        rfl
      simpa only [RingEquiv.mapMatrix_apply, Matrix.map_mul, hadj, hform] using h)

@[expose] def rotation (J : HermitianForm 2 F) (hJ : J.form = !![0,1;1,0])
    (r : Fˣ) (i : F) (hr : J.conj (r:F) = -(r:F)) (hfix : J.conj i = i)
    (hi : i^2 = -1) (h2 : (2:F) ≠ 0) : J.unitarySubgroup :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (rotationMatrix r i)
      (by rw [rotation_det r i hi h2]; exact one_ne_zero),
    rotation_unitary J hJ r i hr hfix hi h2⟩

theorem rotation_coboundary (J : HermitianForm 2 F) (hJ : J.form = !![0,1;1,0])
    (r : Fˣ) (i : F) (hr : J.conj (r:F) = -(r:F)) (hfix : J.conj i = i)
    (hi : i^2 = -1) (h2 : (2:F) ≠ 0) :
    let R := rotation J hJ r i hr hfix hi h2
    R * (fieldConj J hJ R)⁻¹ = torus J hJ r hr * swap J hJ := by
  dsimp only
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rotation, rotationMatrix, fieldConj, torus, torusGL, swap,
      GeneralLinearGroup.diagonalPair, GeneralLinearGroup.coordinateSwap,
      mul_apply, Fin.sum_univ_two, hr, hfix, map_ofNat] <;> field_simp

theorem swap_inverts_conjugate_torus (J : HermitianForm 2 F)
    (hJ : J.form = !![0,1;1,0]) (r : Fˣ)
    (hr : J.conj (r:F) = -(r:F)) :
    swap J hJ * fieldConj J hJ (torus J hJ r hr) * (swap J hJ)⁻¹ =
      (torus J hJ r hr)⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [fieldConj, torus, torusGL, swap, GeneralLinearGroup.diagonalPair,
      GeneralLinearGroup.coordinateSwap, mul_apply, vecMul, dotProduct,
      Fin.sum_univ_two, hr]

theorem rotation_special (J : HermitianForm 2 F) (hJ : J.form = !![0,1;1,0])
    (r : Fˣ) (i : F) (hr : J.conj (r:F) = -(r:F)) (hfix : J.conj i = i)
    (hi : i^2 = -1) (h2 : (2:F) ≠ 0) :
    (rotation J hJ r i hr hfix hi h2).val ∈ J.specialSubgroup := by
  refine ⟨(rotation J hJ r i hr hfix hi h2).property, ?_⟩
  apply Units.ext
  exact rotation_det r i hi h2

section Ambient
variable {G : Type*} [Group G]

theorem rotation_conjugates_actor (J : HermitianForm 2 F)
    (hJ : J.form = !![0,1;1,0]) (r : Fˣ) (i : F)
    (hr : J.conj (r:F) = -(r:F)) (hfix : J.conj i = i)
    (hi : i^2 = -1) (h2 : (2:F) ≠ 0)
    (f : J.unitarySubgroup →* G) (c : G)
    (hc : ∀ u, c * f u * c⁻¹ = f (fieldConj J hJ u)) :
    let g := f (rotation J hJ r i hr hfix hi h2)
    g * c * g⁻¹ = f (torus J hJ r hr) * f (swap J hJ) * c := by
  let R := rotation J hJ r i hr hfix hi h2
  have hR := congrArg f (rotation_coboundary J hJ r i hr hfix hi h2)
  change f (R * (fieldConj J hJ R)⁻¹) = f (torus J hJ r hr * swap J hJ) at hR
  simp only [map_mul, map_inv] at hR
  change f R * c * (f R)⁻¹ = _
  calc
    _ = (f R * (c * f R * c⁻¹)⁻¹) * c := by group
    _ = _ := by rw [hc, hR]

theorem twisted_swap_inverts_torus (J : HermitianForm 2 F)
    (hJ : J.form = !![0,1;1,0]) (r : Fˣ)
    (hr : J.conj (r:F) = -(r:F)) (f : J.unitarySubgroup →* G) (c : G)
    (hc : ∀ u, c * f u * c⁻¹ = f (fieldConj J hJ u)) :
    let a := f (torus J hJ r hr)
    let b := f (swap J hJ)
    (a*b*c) * a * (a*b*c)⁻¹ = a⁻¹ := by
  have hh := congrArg f (swap_inverts_conjugate_torus J hJ r hr)
  simp only [map_mul, map_inv] at hh
  dsimp only
  calc
    _ = f (torus J hJ r hr) *
        (f (swap J hJ) * (c * f (torus J hJ r hr) * c⁻¹) * (f (swap J hJ))⁻¹) *
        (f (torus J hJ r hr))⁻¹ := by group
    _ = _ := by rw [hc, hh]; group

end Ambient

@[expose] def quaternionJ (i : F) : Matrix (Fin 2) (Fin 2) F := !![i,0;0,-i]

@[expose] def quaternionK (r : Fˣ) (i : F) : Matrix (Fin 2) (Fin 2) F :=
  !![0,-(r:F)*i; -((r:F)⁻¹)*i,0]

theorem quaternion_relations (r : Fˣ) (i : F) (hi : i^2 = -1) :
    quaternionJ i * quaternionJ i = -1 ∧
    quaternionK r i * quaternionK r i = -1 ∧
    quaternionJ i * quaternionK r i = -(quaternionK r i * quaternionJ i) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [quaternionJ, quaternionK, mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring_nf <;> simp [hi]

theorem quaternionK_eq (r : Fˣ) (i : F) :
    quaternionK r i = (torusGL r).val * (GeneralLinearGroup.coordinateSwap F).val *
      quaternionJ i := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [quaternionJ, quaternionK, torusGL, GeneralLinearGroup.diagonalPair,
      GeneralLinearGroup.coordinateSwap, mul_apply, Fin.sum_univ_two]

theorem rotation_formula (r : Fˣ) (i : F) (hi : i^2 = -1) :
    rotationMatrix r i = (2:F)⁻¹ •
      (1 + quaternionJ i + quaternionK r i + quaternionJ i * quaternionK r i) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rotationMatrix, quaternionJ, quaternionK] <;>
    ring_nf <;> simp [hi, sub_eq_add_neg]

theorem rotation_intertwines (r : Fˣ) (i : F) :
    rotationMatrix r i * quaternionJ i = quaternionK r i * rotationMatrix r i := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rotationMatrix, quaternionJ, quaternionK, mul_apply, Fin.sum_univ_two] <;>
    field_simp

@[expose] def minusOne (J : HermitianForm 2 F) (hJ : J.form = !![0,1;1,0]) :
    J.unitarySubgroup :=
  ⟨GeneralLinearGroup.scalar (Fin 2) (-1), by
    rw [J.mem_unitarySubgroup_iff]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [GeneralLinearGroup.coe_scalar, scalar_apply, HermitianForm.conjTranspose,
        hJ, mul_apply, Fin.sum_univ_two]⟩

theorem minusOne_commute (J : HermitianForm 2 F) (hJ : J.form = !![0,1;1,0])
    (u : J.unitarySubgroup) : minusOne J hJ * u = u * minusOne J hJ := by
  apply Subtype.ext
  exact GeneralLinearGroup.scalar_commute (-1) u.val

end Matrix.UnitaryQuaternionRotation
