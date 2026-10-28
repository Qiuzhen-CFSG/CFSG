module
public import Theory.GroupAction.SylowNormalizerDisplacements
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors

/-!
# The scalar obstruction for the degree-one special-unitary enlargement

The SU₃(2) center has odd order. Normalizer displacements therefore fix it.
Every unit of the field of four elements gives a scalar special-unitary
matrix, so fixation of that center forces the field parameter of any actual
semilinear formula to be identity. Multiplying a unitary matrix's cube by
the inverse determinant gives a special-unitary matrix with the same
conjugation. Thus the diagonal outer image has exponent three and a
two-power actor satisfying the formula is inner, without perfectness.

The existence of a semilinear formula for an arbitrary SU₃(2) automorphism
is not asserted here. The literal DGS local action is the consumer in
LocalStructure.SmallSpecialUnitaryAction; its coverage remains a source
obligation. No conclusion is drawn for the centerless PSU₃(2) case.
Source: DGS, Groups and Graphs (1985), 6.1, pp.118--119; the scalar matrix
and determinant calculations are those of Huppert II.10.12.
-/

public noncomputable section
open Subgroup Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.SmallSpecialNormalizer
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

private def scalarSpecial (hc : Nat.card F = 2^2)
    (hconj : ∀ x, J.conj x = x^2) (k : Fˣ) : J.specialSubgroup :=
  ⟨GeneralLinearGroup.scalar (Fin 3) k,by
    have hk : k^3 = 1 := by simpa [Nat.card_units,hc] using pow_card_eq_one' (x := k)
    refine ⟨J.scalar_mem_unitary_of_norm_one k ?_,?_⟩
    · rw [hconj]
      have hv := congrArg Units.val hk
      change (k : F)^3 = 1 at hv
      simpa only [pow_succ] using hv
    · change GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) k) = 1
      simpa only [GeneralLinearGroup.det_scalar,Fintype.card_fin] using hk⟩

omit [Finite F] in
private theorem scalarSpecial_central (hc : Nat.card F = 2^2)
    (hconj : ∀ x, J.conj x = x^2) (k : Fˣ) :
    scalarSpecial J hc hconj k ∈ center J.specialSubgroup := by
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact mem_center_iff.mp
    (show GeneralLinearGroup.scalar (Fin 3) k ∈ center (GL (Fin 3) F) from by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨k,rfl⟩) x.val

omit [Finite F] in
/-- Over the field of four elements every nonzero scalar belongs to SU₃; fixing these scalars detects the field parameter. -/
theorem field_eq_one_of_center_fixed
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (a : MulAut J.specialSubgroup) (σ : F ≃+* F)
    (hs : J.HasSpecialUnitarySemilinearForm a σ)
    (hz : ∀ z ∈ center J.specialSubgroup, a z = z) : σ = 1 := by
  obtain ⟨u,hu⟩ := hs
  have hunit (k : Fˣ) : σ (k : F) = k := by
    have he := hu (scalarSpecial J hc hconj k)
    rw [hz _ (scalarSpecial_central J hc hconj k)] at he
    have hmap : GeneralLinearGroup.map σ.toRingHom
        (GeneralLinearGroup.scalar (Fin 3) k) =
        GeneralLinearGroup.scalar (Fin 3) (Units.map σ.toMonoidHom k) := by
      apply Units.ext
      ext i j
      by_cases hij : i = j
      · subst j; simp [GeneralLinearGroup.coe_scalar]
      · simp [GeneralLinearGroup.coe_scalar,hij]
    change GeneralLinearGroup.scalar (Fin 3) k =
      u.val * GeneralLinearGroup.map σ.toRingHom
        (GeneralLinearGroup.scalar (Fin 3) k) * u.val⁻¹ at he
    rw [hmap] at he
    have hcent : GeneralLinearGroup.scalar (Fin 3) (Units.map σ.toMonoidHom k) ∈
        center (GL (Fin 3) F) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_,rfl⟩
    rw [mem_center_iff.mp hcent u.val,mul_inv_cancel_right] at he
    have hh := congrArg (fun g : GL (Fin 3) F => g.val 0 0) he
    simpa [GeneralLinearGroup.coe_scalar] using hh.symm
  apply RingEquiv.ext
  intro x
  by_cases hx : x = 0
  · subst x; exact map_zero σ
  · exact hunit (Units.mk0 x hx)

/-- The original small special-unitary Sylow-normalizer condition fixes the full cubic center. -/
theorem fixes_center_of_normalizer_displacements
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (S : Sylow 2 J.specialSubgroup) (a : MulAut J.specialSubgroup)
    (hd : ∀ x ∈ normalizer (S : Set J.specialSubgroup), x⁻¹*a x ∈ S) :
    ∀ z ∈ center J.specialSubgroup, a z = z := by
  apply a.fixes_center_of_sylow_normalizer_displacements S _ hd
  rw [←J.specialToProjective_ker_eq_center
    (EvenProjectiveComparison.center_eq_bot J (n := 1) (by decide)
      (by simpa using hc) (by simpa using hconj))]
  exact J.odd_card_specialToProjective_ker

/-- Any actual semilinear formula for such an actor has identity field parameter. -/
theorem field_eq_one_of_normalizer_displacements
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (S : Sylow 2 J.specialSubgroup) (a : MulAut J.specialSubgroup)
    (hd : ∀ x ∈ normalizer (S : Set J.specialSubgroup), x⁻¹*a x ∈ S)
    (σ : F ≃+* F) (hs : J.HasSpecialUnitarySemilinearForm a σ) : σ = 1 :=
  field_eq_one_of_center_fixed J hc hconj a σ hs
    (fixes_center_of_normalizer_displacements J hc hconj S a hd)

omit [Finite F] in
private theorem inner_cube_of_unitary_formula
    (a : MulAut J.specialSubgroup) (u : J.unitarySubgroup)
    (hu : ∀ x : J.specialSubgroup, (a x).val = u.val*x.val*u.val⁻¹) :
    a^3 ∈ MulAut.innerSubgroup J.specialSubgroup := by
  let d := GeneralLinearGroup.det u.val
  have hd : J.conj ((d⁻¹ : Fˣ) : F) * ((d⁻¹ : Fˣ) : F) = 1 := by
    simp only [Units.val_inv_eq_inv_val,d,GeneralLinearGroup.val_det_apply]
    rw [map_inv₀,←mul_inv,J.unitary_det_norm_one,inv_one]
  let c := GeneralLinearGroup.scalar (Fin 3) d⁻¹
  let v : J.specialSubgroup := ⟨c*u.val^3,by
    refine ⟨J.unitarySubgroup.mul_mem (J.scalar_mem_unitary_of_norm_one d⁻¹ hd)
      (J.unitarySubgroup.pow_mem u.property 3),?_⟩
    change GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) d⁻¹*u.val^3)=1
    simp [map_mul,map_pow,GeneralLinearGroup.det_scalar,d]⟩
  refine ⟨v,?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change (c*u.val^3)*x.val*(c*u.val^3)⁻¹ = (a (a (a x))).val
  rw [hu,hu,hu]
  have hc := GeneralLinearGroup.scalar_commute d⁻¹ (u.val^3*x.val*(u.val^3)⁻¹)
  change c*(u.val^3*x.val*(u.val^3)⁻¹) = (u.val^3*x.val*(u.val^3)⁻¹)*c at hc
  calc
    _ = c*(u.val^3*x.val*(u.val^3)⁻¹)*c⁻¹ := by group
    _ = u.val^3*x.val*(u.val^3)⁻¹ := by rw [hc,mul_inv_cancel_right]
    _ = _ := by simp only [pow_succ,pow_zero]; group

/-- After the scalar calculation, the diagonal quotient has exponent three, so a two-power actor is inner. Semilinear existence remains explicit. -/
theorem inner_of_semilinear_normalizer_displacements
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (S : Sylow 2 J.specialSubgroup) (a : MulAut J.specialSubgroup)
    {r : ℕ} (ha : a^(2^r)=1)
    (hd : ∀ x ∈ normalizer (S : Set J.specialSubgroup), x⁻¹*a x ∈ S)
    (hs : ∃ σ : F ≃+* F, J.HasSpecialUnitarySemilinearForm a σ) :
    a ∈ MulAut.innerSubgroup J.specialSubgroup := by
  obtain ⟨σ,hs⟩ := hs
  have he := field_eq_one_of_normalizer_displacements J hc hconj S a hd σ hs
  obtain ⟨u,hu⟩ := hs
  have hf (x : J.specialSubgroup) : (a x).val = u.val*x.val*u.val⁻¹ := by
    have hsid : σ.toRingHom = RingHom.id F := by rw [he]; rfl
    simpa only [hsid,GeneralLinearGroup.map_id,MonoidHom.id_apply] using hu x
  have hcube := inner_cube_of_unitary_formula J a u hf
  let q := QuotientGroup.mk' (MulAut.innerSubgroup J.specialSubgroup)
  have hq3 : (q a)^3=1 := by
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hcube
  have hq2 : (q a)^(2^r)=1 := by rw [←map_pow,ha,map_one]
  exact (QuotientGroup.eq_one_iff a).mp
    ((pow_eq_one_iff_of_coprime ((by decide : Nat.Coprime 2 3).pow_left r)).mp ⟨hq2,hq3⟩)
end BenderSuzuki.MatrixGroups.HermitianForm.SmallSpecialNormalizer
