module

public import Theory.SpecificGroups.ClassicalUnitary.FiveFlag
public import Theory.FieldTheory.RootsOfUnityCard

/-!
# The scalar kernel of SU₅(4) → PSU₅(4)

For any nondegenerate Hermitian form with fourth-power conjugation, the
scalar special-unitary matrices are exactly the fifth roots of unity.
They identify the kernel of the actual map to PGL. Over a field of order
sixteen this kernel has order five, and it lies in every subspace stabilizer.
Thus each projective stabilizer has one fifth the order of its SU preimage.

Source: the projective unitary convention in Aschbacher–Smith,
Theorem 0.1.2(1), and the parabolics of F.1.12(7), printed pp.4 and 263–264.
The calculation works for arbitrary stored Hermitian matrices.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive
variable {F : Type*} [Field F] (J : HermitianForm 5 F)
  (hconj : ∀ x, J.conj x = x ^ 4)

/-- The projective kernel is central in the actual SU group. -/
theorem project_kernel_le_center : (project J).ker ≤ Subgroup.center J.specialSubgroup := by
  intro A hA
  have hz : A.val ∈ Subgroup.center (GL (Fin 5) F) := by
    apply ProjGenLinGroup.mk_eq_one.mp
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hA)
  exact Subgroup.mem_center_iff.mpr fun B =>
    Subtype.ext (Subgroup.mem_center_iff.mp hz B.val)

include hconj

/-- Fifth-root scalar matrices satisfy both unitary and determinant-one equations. -/
theorem scalar_special (u : rootsOfUnity 5 F) :
    GeneralLinearGroup.scalar (Fin 5) u.val ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  have hu : (u.val : F) ^ 5 = 1 := (mem_rootsOfUnity' 5 u.val).mp u.property
  constructor
  · have ha : J.conjTranspose (GeneralLinearGroup.scalar (Fin 5) u.val).val =
        diagonal (fun _ => J.conj (u.val : F)) := by
      ext i j
      by_cases h : i = j <;>
        simp [HermitianForm.conjTranspose, GeneralLinearGroup.coe_scalar,
          Matrix.scalar, h, Ne.symm]
    rw [ha, GeneralLinearGroup.coe_scalar]
    ext i j
    change (diagonal (fun _ : Fin 5 => J.conj (u.val : F)) * J.form *
      diagonal (fun _ : Fin 5 => (u.val : F))) i j = J.form i j
    simp only [diagonal_mul, mul_diagonal]
    rw [hconj]
    calc
      (u.val : F) ^ 4 * J.form i j * (u.val : F) =
        (u.val : F) ^ 5 * J.form i j := by ring
      _ = J.form i j := by rw [hu, one_mul]
  · simpa using (mem_rootsOfUnity 5 u.val).mp u.property

/-- The scalar map with codomain restricted to the projective kernel. -/
noncomputable def scalarToKernel : rootsOfUnity 5 F →* (project J).ker where
  toFun u := ⟨⟨GeneralLinearGroup.scalar (Fin 5) u.val, scalar_special J hconj u⟩, by
    apply Subtype.ext
    exact ProjGenLinGroup.mk_scalar u.val⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_one (GeneralLinearGroup.scalar (Fin 5))
  map_mul' u v := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul (GeneralLinearGroup.scalar (Fin 5)) u.val v.val

/-- Every projectively trivial special-unitary matrix is one of these scalars. -/
theorem scalarToKernel_bijective : Function.Bijective (scalarToKernel J hconj) := by
  constructor
  · intro u v h
    apply Subtype.ext
    apply Units.ext
    have he := congrArg (fun A : (project J).ker => (A.val.val : Matrix (Fin 5) (Fin 5) F) 0 0) h
    simpa [scalarToKernel, GeneralLinearGroup.coe_scalar, Matrix.scalar] using he
  · intro A
    have hA : ProjGenLinGroup.mk A.val.val = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp A.property)
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hA
    obtain ⟨u, hu⟩ := hA
    have hd := (J.mem_specialSubgroup_iff A.val.val).mp A.val.property |>.2
    rw [← hu, GeneralLinearGroup.det_scalar] at hd
    have hr : u ∈ rootsOfUnity 5 F := (mem_rootsOfUnity 5 u).mpr (by simpa using hd)
    refine ⟨⟨u, hr⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hu

/-- The actual projective kernel, identified multiplicatively with fifth roots. -/
noncomputable def scalarKernelEquiv : rootsOfUnity 5 F ≃* (project J).ker :=
  MulEquiv.ofBijective (scalarToKernel J hconj) (scalarToKernel_bijective J hconj)

/-- The scalar factor has order five over the field of sixteen elements. -/
theorem card_project_kernel [Finite F] (hcard : Nat.card F = 16) :
    Nat.card (project J).ker = 5 := by
  rw [← Nat.card_congr (scalarKernelEquiv J hconj).toEquiv]
  apply FiniteField.card_rootsOfUnity_of_dvd
  rw [hcard]
  decide

/-- The scalar factor lies in every subspace stabilizer, so the order drops by five. -/
theorem card_specialStabilizer [Finite F] (hcard : Nat.card F = 16)
    (W : Submodule F (Fin 5 → F)) :
    Nat.card (specialStabilizer J W) = 5 * Nat.card (parabolic J W) := by
  let S := specialStabilizer J W
  let f := (project J).comp S.subtype
  have he : f.ker ≃* (project J).ker :=
    Subgroup.subgroupOfEquivOfLe (ker_project_le_specialStabilizer J W)
  have hk : Nat.card f.ker = 5 :=
    (Nat.card_congr he.toEquiv).trans (card_project_kernel J hconj hcard)
  have hc := f.ker.card_mul_index
  rw [hk, Subgroup.index_ker] at hc
  simpa only [f, MonoidHom.range_comp, Subgroup.range_subtype, S, parabolic] using hc.symm

end Theory.SpecificGroups.UnitaryFive
