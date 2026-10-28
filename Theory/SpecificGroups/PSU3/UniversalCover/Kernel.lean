module

public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The scalar kernel of SU₃ → PSU₃

For any stored nondegenerate Hermitian form, a scalar matrix is special
unitary exactly when its scalar has norm one and cube one. With involution
`x ↦ x^q`, these scalars are the `gcd(3,q+1)`-st roots of unity. The scalar
map gives an actual multiplicative equivalence with the projection kernel;
finite-field cyclicity then identifies it with the corresponding `ZMod` group.

The calculation uses a nonzero entry of the original form, so requires no
basis change. It applies to the literal projective image in PGL. Universality
is a separate obligation in the importing `UniversalCover` module.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.1.3(2)
and I.1.4(2), printed pp.407–408; GLS3, Table 6.1.2 (canonical unitary center).
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover
variable {F : Type*} [Field F] (J : HermitianForm 3 F)

private theorem conjTranspose_scalar (u : Fˣ) :
    J.conjTranspose (Matrix.scalar (Fin 3) (u : F)) =
      Matrix.scalar (Fin 3) (J.conj (u : F)) := by
  ext i j
  by_cases h : i = j
  · subst j; simp [HermitianForm.conjTranspose, Matrix.scalar_apply]
  · simp [HermitianForm.conjTranspose, Matrix.scalar_apply, h, Ne.symm h]

/-- A scalar is special unitary precisely when its norm and determinant are one. -/
theorem scalar_mem_special_iff (u : Fˣ) :
    GeneralLinearGroup.scalar (Fin 3) u ∈ J.specialSubgroup ↔
      J.conj (u : F) * (u : F) = 1 ∧ u ^ 3 = 1 := by
  rw [J.mem_specialSubgroup_iff, GeneralLinearGroup.det_scalar]
  simp only [Fintype.card_fin]
  apply and_congr_left
  intro _
  change J.conjTranspose (Matrix.scalar (Fin 3) (u : F)) * J.form *
    Matrix.scalar (Fin 3) (u : F) = J.form ↔ _
  rw [conjTranspose_scalar]
  constructor
  · intro h
    obtain ⟨j, hj⟩ : ∃ j, J.form 0 j ≠ 0 := by
      by_contra! h
      exact J.form_nondegenerate (Matrix.det_eq_zero_of_row_eq_zero 0 h)
    have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 j) h
    simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    apply mul_right_cancel₀ hj
    calc
      (J.conj (u : F) * (u : F)) * J.form 0 j =
          J.conj (u : F) * J.form 0 j * (u : F) := by ring
      _ = J.form 0 j := he
      _ = 1 * J.form 0 j := (one_mul _).symm
  · intro h
    ext i j
    simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    calc
      J.conj (u : F) * J.form i j * (u : F) =
          (J.conj (u : F) * (u : F)) * J.form i j := by ring
      _ = J.form i j := by rw [h, one_mul]

/-- The scalar conditions are exactly the common third and `(q+1)`-st roots of unity. -/
theorem scalar_mem_special_iff_roots {q : ℕ}
    (hconj : ∀ x, J.conj x = x ^ q) (u : Fˣ) :
    GeneralLinearGroup.scalar (Fin 3) u ∈ J.specialSubgroup ↔
      u ∈ rootsOfUnity (Nat.gcd 3 (q + 1)) F := by
  rw [scalar_mem_special_iff, ← rootsOfUnity_inf_rootsOfUnity (M := F),
    Subgroup.mem_inf, mem_rootsOfUnity, mem_rootsOfUnity]
  rw [and_comm]
  apply and_congr_right
  intro _
  rw [hconj, ← pow_succ]
  constructor
  · exact fun h => Units.ext h
  · exact fun h => congrArg Units.val h

/-- The scalar map into the literal projective kernel. -/
def rootsToKernel {q : ℕ} (hconj : ∀ x, J.conj x = x ^ q) :
    rootsOfUnity (Nat.gcd 3 (q + 1)) F →* J.specialToProjective.ker where
  toFun u := ⟨⟨GeneralLinearGroup.scalar (Fin 3) u.val,
    (scalar_mem_special_iff_roots J hconj u.val).mpr u.property⟩, by
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      rw [J.specialToProjective_apply_val, Subgroup.coe_one]
      apply ProjGenLinGroup.mk_eq_one.mpr
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u.val, rfl⟩⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one _
  map_mul' u v := by apply Subtype.ext; apply Subtype.ext; exact map_mul _ _ _

/-- Every element of the literal projective kernel has a unique scalar parameter. -/
theorem rootsToKernel_bijective {q : ℕ} (hconj : ∀ x, J.conj x = x ^ q) :
    Function.Bijective (rootsToKernel J hconj) := by
  constructor
  · intro u v h
    apply Subtype.ext
    apply Units.ext
    have he := congrArg (fun z : J.specialToProjective.ker => z.val.val.val 0 0) h
    simpa [rootsToKernel, GeneralLinearGroup.scalar, Matrix.scalar_apply] using he
  · intro x
    have hz : x.val.val ∈ center (GL (Fin 3) F) := by
      apply ProjGenLinGroup.mk_eq_one.mp
      simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
        congrArg Subtype.val (MonoidHom.mem_ker.mp x.property)
    rw [GeneralLinearGroup.center_eq_range_scalar] at hz
    obtain ⟨u, hu⟩ := hz
    refine ⟨⟨u, (scalar_mem_special_iff_roots J hconj u).mp (hu ▸ x.val.property)⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hu

/-- Scalar parameters identify the actual projection kernel with roots of unity. -/
noncomputable def kernelEquivRoots {q : ℕ} (hconj : ∀ x, J.conj x = x ^ q) :
    J.specialToProjective.ker ≃* rootsOfUnity (Nat.gcd 3 (q + 1)) F :=
  (MulEquiv.ofBijective (rootsToKernel J hconj) (rootsToKernel_bijective J hconj)).symm

/-- The inverse equivalence uses the specified scalar matrix in the original basis. -/
@[simp] theorem kernelEquivRoots_symm_apply_val {q : ℕ}
    (hconj : ∀ x, J.conj x = x ^ q)
    (u : rootsOfUnity (Nat.gcd 3 (q + 1)) F) :
    ((kernelEquivRoots J hconj).symm u).val.val =
      GeneralLinearGroup.scalar (Fin 3) u.val := by rfl

variable [Finite F]

/-- The exact scalar-kernel order for every nondegenerate Hermitian form. -/
theorem card_kernel {q : ℕ} (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) :
    Nat.card J.specialToProjective.ker = Nat.gcd 3 (q + 1) := by
  rw [Nat.card_congr (kernelEquivRoots J hconj).toEquiv,
    rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker, Nat.card_units, hcard]
  apply Nat.gcd_eq_right
  have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq q 1
  rw [hfactor]
  exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right 3 (q + 1)) _

/-- The projection kernel as a cyclic group, retaining its multiplicative structure. -/
noncomputable def kernelEquivCyclic {q : ℕ} (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) :
    J.specialToProjective.ker ≃* Multiplicative (ZMod (Nat.gcd 3 (q + 1))) := by
  let : IsCyclic J.specialToProjective.ker := (kernelEquivRoots J hconj).isCyclic.mpr inferInstance
  exact mulEquivOfCyclicCardEq (by
    change Nat.card J.specialToProjective.ker = Nat.card (ZMod (Nat.gcd 3 (q + 1)))
    rw [card_kernel J hcard hconj, Nat.card_zmod])

/-- The kernel is cyclic of order three when `q ≡ -1 mod 3`. -/
noncomputable def kernelEquivThree {q : ℕ} (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) (hq : q % 3 = 2) :
    J.specialToProjective.ker ≃* Multiplicative (ZMod 3) := by
  have hg : Nat.gcd 3 (q + 1) = 3 := by
    rw [Nat.gcd_comm]
    apply Nat.gcd_eq_right_iff_dvd.mpr
    exact Nat.dvd_of_mod_eq_zero (by omega)
  exact cast (congrArg (fun d => J.specialToProjective.ker ≃* Multiplicative (ZMod d)) hg)
    (kernelEquivCyclic J hcard hconj)

/-- In all other congruence classes the projection kernel is trivial. -/
noncomputable def kernelEquivOne {q : ℕ} (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) (hq : q % 3 ≠ 2) :
    J.specialToProjective.ker ≃* Multiplicative (ZMod 1) := by
  have hg : Nat.gcd 3 (q + 1) = 1 := by
    apply Nat.Coprime.gcd_eq_one
    apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr
    intro hd
    have hm := Nat.mod_eq_zero_of_dvd hd
    omega
  exact cast (congrArg (fun d => J.specialToProjective.ker ≃* Multiplicative (ZMod d)) hg)
    (kernelEquivCyclic J hcard hconj)
end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover
