module

public import Theory.SpecificGroups.SU3.FullTorusNormalizer
public import Theory.SpecificGroups.SU3.ProjectiveEntrywiseAction

/-!
# The full cyclic torus in a scalar unitary cover

The full special-unitary torus contains every projective scalar. Its image
is the full projective torus, so it is exactly that torus's preimage. In
any quotient of SU₃ over the same PSU₃ marking, the corresponding preimage
torus is therefore cyclic. The image of the special Weyl element normalizes
it and remains outside the preimage of the marked Borel.

Source: Huppert II.10.12 and Aschbacher–Smith 4.4.13(1), pp.623–624.
The matrix calculation retains the full quadratic-field torus.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Theory.SpecificGroups.UnitaryBorel
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

theorem projection_torus (a : Eˣ) :
    J.specialToProjective (hermitianTorusSU J hJ a) = hermitianTorusPSU J hJ a := by
  apply Subtype.ext
  rw [J.specialToProjective_apply_val, hermitianTorusPSU_val]
  rfl

theorem projection_weyl :
    J.specialToProjective (hermitianWeylSU J hJ) = hermitianWeylPSU J hJ := by
  apply Subtype.ext
  rw [J.specialToProjective_apply_val, hermitianWeylPSU_val]
  rfl

theorem specialTorus_map_projection :
    (hermitianTorusSU J hJ).range.map J.specialToProjective =
      (hermitianTorusPSU J hJ).range := by
  rw [← MonoidHom.range_comp]
  congr 1
  exact MonoidHom.ext (projection_torus J hJ)

theorem projection_kernel_le_specialTorus :
    J.specialToProjective.ker ≤ (hermitianTorusSU J hJ).range := by
  intro x hx
  have hxc : x.val ∈ Subgroup.center (GL (Fin 3) E) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hxc
  obtain ⟨k,hk⟩ := hxc
  have hspecial := (J.mem_specialSubgroup_iff (x : GL (Fin 3) E)).mp x.property
  rw [← hk] at hspecial
  have hu := congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A 0 2) hspecial.1
  have hn : J.conj (k : E) * (k : E) = 1 := by
    simpa [hJ, HermitianForm.conjTranspose, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_three] using hu
  have hd := congrArg (fun a : Eˣ => (a : E)) hspecial.2
  have hcube : (k : E) ^ 3 = 1 := by
    simpa [Matrix.GeneralLinearGroup.det, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.det_fin_three, pow_succ, pow_two] using hd
  have h0 : (J.conj (k : E))⁻¹ = (k : E) := inv_eq_of_mul_eq_one_right hn
  have hci : J.conj (k : E) = (k : E)⁻¹ := eq_inv_of_mul_eq_one_left hn
  have h1 : J.conj (k : E) * (k : E)⁻¹ = (k : E) := by
    rw [hci]
    field_simp
    simpa [pow_succ,pow_two] using hcube.symm
  refine ⟨k,?_⟩
  apply Subtype.ext
  rw [← hk]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change hermitianTorusMatrix J k i j = (Matrix.scalar (Fin 3) (k : E)) i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusMatrix,Matrix.scalar_apply,h0,h1]

/-- The whole projective torus lifts to the full cyclic special torus. -/
theorem projectiveTorus_preimage :
    (hermitianTorusPSU J hJ).range.comap J.specialToProjective =
      (hermitianTorusSU J hJ).range := by
  rw [← specialTorus_map_projection,comap_map_eq,
    sup_eq_left.mpr (projection_kernel_le_specialTorus J hJ)]

theorem specialWeyl_mul_torus (a : Eˣ) :
    hermitianWeylSU J hJ * hermitianTorusSU J hJ a =
      hermitianTorusSU J hJ ((Units.map J.conj.toMonoidHom a)⁻¹) *
        hermitianWeylSU J hJ := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusSU,hermitianWeylSU,hermitianTorusGL,hermitianTorusMatrix,
      hermitianWeylGL,hermitianWeylMatrix,Matrix.mul_apply,Fin.sum_univ_three,
      J.conj_involutive (a : E),mul_comm]

variable {L : Type*} [Group L]

/-- A scalar-cover quotient retains the literal full preimage torus. -/
theorem specialTorus_image_of_scalar_lift
    (r : L →* ProjectiveSpecialUnitaryMatrixGroup J) (k : J.specialSubgroup →* L)
    (hk : Function.Surjective k) (hfac : r.comp k = J.specialToProjective) :
    (hermitianTorusSU J hJ).range.map k = (hermitianTorusPSU J hJ).range.comap r := by
  have he : ((hermitianTorusPSU J hJ).range.comap r).comap k =
      (hermitianTorusSU J hJ).range := by
    rw [comap_comap,hfac,projectiveTorus_preimage]
  rw [← he,map_comap_eq_self_of_surjective hk]

variable [Finite E]

theorem fullTorus_preimage_isCyclic_of_scalar_lift
    (r : L →* ProjectiveSpecialUnitaryMatrixGroup J) (k : J.specialSubgroup →* L)
    (hk : Function.Surjective k) (hfac : r.comp k = J.specialToProjective) :
    IsCyclic ((hermitianTorusPSU J hJ).range.comap r) := by
  rw [← specialTorus_image_of_scalar_lift J hJ r k hk hfac]
  let : IsCyclic (hermitianTorusSU J hJ).range :=
    isCyclic_of_surjective _ (hermitianTorusSU J hJ).rangeRestrict_surjective
  exact isCyclic_of_surjective _ (k.subgroupMap_surjective _)

/-- The actual Weyl image normalizes the full preimage torus and escapes
the actual preimage Borel, including when the scalar prime is three. -/
theorem scalar_weyl_escape
    (r : L →* ProjectiveSpecialUnitaryMatrixGroup J) (k : J.specialSubgroup →* L)
    (hk : Function.Surjective k) (hfac : r.comp k = J.specialToProjective) :
    k (hermitianWeylSU J hJ) ∈
        normalizer ((hermitianTorusPSU J hJ).range.comap r : Set L) ∧
      k (hermitianWeylSU J hJ) ∉ (BenderBorel.unitaryBorel J hJ).comap r := by
  have hn : hermitianWeylSU J hJ ∈ normalizer ((hermitianTorusSU J hJ).range : Set _) := by
    apply mem_normalizer_fintype
    rintro _ ⟨a,rfl⟩
    refine ⟨(Units.map J.conj.toMonoidHom a)⁻¹,?_⟩
    rw [specialWeyl_mul_torus,mul_inv_cancel_right]
  constructor
  · have hh := (hermitianTorusSU J hJ).range.le_normalizer_map k (mem_map_of_mem k hn)
    rwa [specialTorus_image_of_scalar_lift J hJ r k hk hfac] at hh
  · intro hw
    have he : r (k (hermitianWeylSU J hJ)) = hermitianWeylPSU J hJ :=
      (DFunLike.congr_fun hfac _).trans (projection_weyl J hJ)
    exact weyl_not_mem_borel J hJ (he ▸ hw)

end Theory.SpecificGroups.UnitaryBorel
