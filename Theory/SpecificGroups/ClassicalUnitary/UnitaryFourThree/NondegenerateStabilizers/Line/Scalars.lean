module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers.Line.Blocks
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The scalar quotient of GU₃(3)

The determinant of a unitary matrix has norm one, hence fourth power one.
Consequently `B ↦ det(B) • B` is a homomorphism from GU₃(3) onto SU₃(3): its
determinant is `det(B)^4`, and it restricts to the identity on SU₃. Its kernel
is precisely the norm-one scalar matrices, a group of order four.

The scalar kernel of SU₃ → PGL₃ is trivial, since its scalar must have both
third and fourth powers one. Thus the quotient constructed here is the actual
shared projective carrier in dimension three, rather than an abstract tag.
Source: GLS3, chapter 2, §2.7 (`refs/KGroup/GLS3/chapter2.tex`), unitary and
projective conventions. These calculations provide the projective correction
for the nondegenerate-line stabilizer in PSU₄(3).
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers.Line

abbrev SpecialUnitaryThree := (form 3).specialSubgroup

private theorem scalar_matrix (n : ℕ) (u : FiniteField.Nineˣ) :
    (GeneralLinearGroup.scalar (Fin n) u).val = u.val • (1 : Matrix (Fin n) (Fin n) FiniteField.Nine) := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;> simp [GeneralLinearGroup.coe_scalar, Matrix.scalar,
    h]

private theorem scalar_unitary (n : ℕ) (u : FiniteField.Nineˣ) (hu : star u.val * u.val = 1) :
    GeneralLinearGroup.scalar (Fin n) u ∈ (form n).unitarySubgroup := by
  change (GeneralLinearGroup.scalar (Fin n) u).val.conjTranspose * 1 *
    (GeneralLinearGroup.scalar (Fin n) u).val = 1
  rw [scalar_matrix, mul_one, conjTranspose_smul, conjTranspose_one, Matrix.smul_mul,
    Matrix.mul_smul, mul_one, smul_smul, hu, one_smul]

/-- Multiplication by the determinant maps GU₃(3) onto SU₃(3). -/
def correction : FullUnitaryThree →* SpecialUnitaryThree where
  toFun B := ⟨GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det B.val) * B.val, by
    rw [(form 3).mem_specialSubgroup_iff]
    constructor
    · exact (form 3).unitarySubgroup.mul_mem
        (scalar_unitary 3 _ (det_norm B)) B.property
    · rw [map_mul, GeneralLinearGroup.det_scalar]
      apply Units.ext
      change B.val.val.det ^ 3 * B.val.val.det = 1
      rw [← pow_succ, det_pow_four]⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' B C := by
    apply Subtype.ext
    change GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det (B.val * C.val)) *
      (B.val * C.val) =
      (GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det B.val) * B.val) *
      (GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det C.val) * C.val)
    rw [GeneralLinearGroup.det.map_mul,
      (GeneralLinearGroup.scalar (Fin 3)).map_mul]
    calc
      _ = GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det B.val) *
        ((GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det C.val) * B.val) * C.val) := by
          simp only [mul_assoc]
      _ = _ := by
        rw [GeneralLinearGroup.scalar_commute (GeneralLinearGroup.det C.val) B.val]
        simp only [mul_assoc]

theorem correction_val (B : FullUnitaryThree) :
    (correction B).val.val = B.val.val.det • B.val.val := by
  change (GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det B.val)).val * B.val.val = _
  rw [scalar_matrix, Matrix.smul_mul, one_mul]
  rfl

theorem correction_surjective : Function.Surjective correction := by
  intro C
  refine ⟨⟨C.val, C.property.1⟩, ?_⟩
  apply Subtype.ext
  change GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det C.val) * C.val = C.val
  rw [C.property.2, map_one, one_mul]

/-- A scalar in SU₃ has both third and fourth powers one, hence is trivial. -/
theorem project_three_injective : Function.Injective (project 3) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro C hC
  have hp : ProjGenLinGroup.mk C.val = 1 := congrArg Subtype.val hC
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hp
  obtain ⟨u, hu⟩ := hp
  have hd : u ^ 3 = 1 := by
    have h := ((form 3).mem_specialSubgroup_iff C.val).mp C.property |>.2
    rw [← hu, GeneralLinearGroup.det_scalar] at h
    simpa using h
  have hnorm : u.val ^ 4 = 1 := by
    have h := C.property.1
    change C.val.val.conjTranspose * 1 * C.val.val = 1 at h
    rw [← hu, scalar_matrix] at h
    have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) FiniteField.Nine => M 0 0) h
    simpa [FiniteField.Nine.star_eq_cube, ← pow_succ', mul_comm] using he
  have hu1 : u = 1 := by
    apply Units.ext
    have hd' : u.val ^ 3 = 1 := congrArg Units.val hd
    rw [pow_succ, hd', one_mul] at hnorm
    exact hnorm
  change C = 1
  apply Subtype.ext
  rw [← hu, hu1, map_one]
  rfl

theorem correction_kernel_iff (B : FullUnitaryThree) :
    B ∈ correction.ker ↔ B.val =
      GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det B.val)⁻¹ := by
  rw [MonoidHom.mem_ker, ← Subtype.val_inj]
  change GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det B.val) * B.val = 1 ↔ _
  rw [mul_eq_one_iff_eq_inv', ← map_inv]

/-- The norm-one scalars in the full unitary group. -/
def scalarUnitary : rootsOfUnity 4 FiniteField.Nine →* FullUnitaryThree where
  toFun u := ⟨GeneralLinearGroup.scalar (Fin 3) u.val, scalar_unitary 3 u.val (by
    rw [FiniteField.Nine.star_eq_cube, ← pow_succ]
    exact (mem_rootsOfUnity' 4 u.val).mp u.property)⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' u v := by apply Subtype.ext; exact map_mul _ _ _

theorem scalarUnitary_val (u : rootsOfUnity 4 FiniteField.Nine) :
    (scalarUnitary u).val = GeneralLinearGroup.scalar (Fin 3) u.val := by rfl

theorem scalarUnitary_injective : Function.Injective scalarUnitary := by
  intro u v h
  apply Subtype.ext
  apply Units.ext
  exact congrArg (fun B : FullUnitaryThree => B.val.val 0 0) h

theorem scalarUnitary_range : scalarUnitary.range = correction.ker := by
  ext B
  constructor
  · rintro ⟨u, rfl⟩
    rw [correction_kernel_iff]
    change GeneralLinearGroup.scalar (Fin 3) u.val =
      GeneralLinearGroup.scalar (Fin 3)
        (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) u.val))⁻¹
    rw [GeneralLinearGroup.det_scalar]
    apply congrArg (GeneralLinearGroup.scalar (Fin 3))
    change u.val = (u.val ^ 3)⁻¹
    apply (eq_inv_iff_mul_eq_one).mpr
    rw [← pow_succ']
    exact u.property
  · intro hB
    have hd : (GeneralLinearGroup.det B.val) ^ 4 = 1 := by
      apply Units.ext
      exact det_pow_four B
    refine ⟨⟨(GeneralLinearGroup.det B.val)⁻¹, ?_⟩, ?_⟩
    · change (GeneralLinearGroup.det B.val)⁻¹ ^ 4 = 1
      rw [inv_pow, hd, inv_one]
    · apply Subtype.ext
      exact ((correction_kernel_iff B).mp hB).symm

/-- All fourth roots of unity, with their multiplication, form the scalar kernel. -/
def scalarKernelEquiv : rootsOfUnity 4 FiniteField.Nine ≃* correction.ker :=
  (MonoidHom.ofInjective scalarUnitary_injective).trans
    (MulEquiv.subgroupCongr scalarUnitary_range)

private def rootValueEquiv : rootsOfUnity 4 FiniteField.Nine ≃ {x : FiniteField.Nine // x ^ 4 = 1} where
  toFun u := ⟨u.val.val, (mem_rootsOfUnity' 4 u.val).mp u.property⟩
  invFun x := rootsOfUnity.mkOfPowEq x.val x.property
  left_inv u := by apply Subtype.ext; apply Units.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

/-- There are exactly four scalars in the determinant-correction kernel. -/
theorem scalarKernel_card : Nat.card correction.ker = 4 := by
  rw [← Nat.card_congr scalarKernelEquiv.toEquiv,
    Nat.card_congr rootValueEquiv, Nat.card_eq_fintype_card]
  decide

/-- The actual quotient of GU₃ by its four norm-one scalars is SU₃. -/
def unitaryQuotientEquiv : FullUnitaryThree ⧸ correction.ker ≃* SpecialUnitaryThree :=
  QuotientGroup.quotientKerEquivOfSurjective correction correction_surjective

/-- The exact comparison with the shared SU image in PGL₃. -/
def specialProjectiveEquiv : SpecialUnitaryThree ≃* Carrier 3 :=
  MulEquiv.ofBijective (project 3) ⟨project_three_injective, project_surjective 3⟩

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers.Line
