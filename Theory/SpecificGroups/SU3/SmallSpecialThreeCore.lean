module
public import Theory.SpecificGroups.SU3.SmallThreeCore
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.GroupTheory.PCoreSurjective

/-!
# The actual small special-unitary three-core and scalar cover

Over the field of four elements all nonzero scalars are unitary with
determinant one. They exhaust the scalar kernel, whose order is therefore
three. Lifting the projective three-core through this three-group kernel
identifies O₃(SU₃(2)) with its literal preimage and gives order twenty-seven.
The restricted projection is surjective onto the actual elementary nine,
with exactly the same scalar denominator.

The original Borel-core action in LocalStructure.SmallUnitaryThreeCore is
the consumer: it acts on this characteristic group and fixes that kernel.
This does not yet assert extraspeciality or automorphism coverage.
Source: DGS, Groups and Graphs (1985), p.104 and 6.1, pp.118--119;
Huppert II.10.12 for the scalar and projective unitary models.
-/

public noncomputable section
open Subgroup Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.SmallThreeCore
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

private def scalarKernel (hc : Nat.card F = 2^2)
    (hconj : ∀ x, J.conj x = x^2) (k : Fˣ) : J.specialToProjective.ker :=
  ⟨⟨GeneralLinearGroup.scalar (Fin 3) k,by
    have hk : k^3 = 1 := by simpa [Nat.card_units,hc] using pow_card_eq_one' (x := k)
    refine ⟨J.scalar_mem_unitary_of_norm_one k ?_,?_⟩
    · rw [hconj]
      have hv := congrArg Units.val hk
      change (k : F)^3 = 1 at hv
      simpa only [pow_succ] using hv
    · change GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) k) = 1
      simpa only [GeneralLinearGroup.det_scalar,Fintype.card_fin] using hk⟩,by
    apply Subtype.ext
    rw [J.specialToProjective_apply_val,Subgroup.coe_one]
    apply ProjGenLinGroup.mk_eq_one.mpr
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨k,rfl⟩⟩

/-- Every nonzero coefficient is a scalar in SU₃(2), so the literal scalar kernel has order three. -/
theorem special_scalar_kernel_card (hc : Nat.card F = 2^2)
    (hconj : ∀ x, J.conj x = x^2) : Nat.card J.specialToProjective.ker = 3 := by
  have hi : Function.Injective (scalarKernel J hc hconj) := by
    intro a b he
    apply Units.ext
    have hh := congrArg (fun z : J.specialToProjective.ker => z.val.val.val 0 0) he
    simpa [scalarKernel,GeneralLinearGroup.coe_scalar] using hh
  have hl := Nat.card_le_card_of_injective _ hi
  rw [Nat.card_units,hc] at hl
  exact le_antisymm (Nat.le_of_dvd (by decide) J.card_specialToProjective_ker_dvd_three) hl

/-- The special three-core is the literal inverse image of the projective three-core. -/
theorem special_core_preimage :
    (pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J)).comap J.specialToProjective =
      pCore 3 J.specialSubgroup := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  apply J.specialToProjective.comap_pCore_of_ker_isPGroup J.specialToProjective_surjective
  exact fun x => ⟨1,by simpa using J.specialToProjective_ker_cube x⟩

omit [Finite F] in
/-- The full canonical scalar kernel belongs to the special three-core. -/
theorem scalar_kernel_le_special_core : J.specialToProjective.ker ≤ pCore 3 J.specialSubgroup :=
  le_sSup ⟨inferInstance,fun x => ⟨1,by simpa using J.specialToProjective_ker_cube x⟩⟩

/-- The actual SU₃(2) three-core has order twenty-seven. -/
theorem special_core_card (hc : Nat.card F = 2^2)
    (hconj : ∀ x, J.conj x = x^2) : Nat.card (pCore 3 J.specialSubgroup) = 27 := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  rw [J.specialToProjective.card_pCore_of_ker_isPGroup J.specialToProjective_surjective
    (fun x => ⟨1,by simpa using J.specialToProjective_ker_cube x⟩),
    special_scalar_kernel_card J hc hconj,(projective_core_structure J hc hconj).1]

/-- The canonical map on the actual characteristic three-cores. -/
@[expose] def specialCoreProjection :
    pCore 3 J.specialSubgroup →* pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (J.specialToProjective.comp (pCore 3 J.specialSubgroup).subtype).codRestrict _ (fun x =>
    (show (pCore 3 J.specialSubgroup).map J.specialToProjective ≤
      pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J) from
        le_sSup ⟨Normal.map inferInstance J.specialToProjective J.specialToProjective_surjective,
          pCore_isPGroup.map J.specialToProjective⟩) (mem_map_of_mem _ x.property))

omit [Finite F] in
/-- No representative is changed by the restricted projection. -/
theorem specialCoreProjection_apply (x : pCore 3 J.specialSubgroup) :
    (specialCoreProjection J x : ProjectiveSpecialUnitaryMatrixGroup J) =
      J.specialToProjective x := rfl

/-- The special three-core covers the full projective three-core. -/
theorem specialCoreProjection_surjective : Function.Surjective (specialCoreProjection J) := by
  intro x
  obtain ⟨y,hy⟩ := J.specialToProjective_surjective x
  have hm : y ∈ pCore 3 J.specialSubgroup := by
    rw [←special_core_preimage J]
    change J.specialToProjective y ∈ pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J)
    rw [hy]
    exact x.property
  exact ⟨⟨y,hm⟩,Subtype.ext hy⟩

omit [Finite F] in
/-- Its kernel is the same original scalar kernel, restricted to the characteristic three-core. -/
theorem specialCoreProjection_ker : (specialCoreProjection J).ker =
    J.specialToProjective.ker.subgroupOf (pCore 3 J.specialSubgroup) := by
  ext x
  exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩

/-- The central denominator in this cover has exactly order three. -/
theorem specialCoreProjection_ker_card (hc : Nat.card F = 2^2)
    (hconj : ∀ x, J.conj x = x^2) : Nat.card (specialCoreProjection J).ker = 3 := by
  rw [specialCoreProjection_ker,
    Nat.card_congr (subgroupOfEquivOfLe (scalar_kernel_le_special_core J)).toEquiv]
  exact special_scalar_kernel_card J hc hconj

omit [Finite F] in
/-- The three-core projection has central kernel, with literal subgroup inclusion. -/
theorem specialCoreProjection_ker_central :
    (specialCoreProjection J).ker ≤ center (pCore 3 J.specialSubgroup) := by
  intro z hz
  have hk : (z : J.specialSubgroup) ∈ J.specialToProjective.ker :=
    congrArg Subtype.val hz
  exact mem_center_iff.mpr fun x => Subtype.ext
    (mem_center_iff.mp (J.specialToProjective_ker_le_center hk) x.val)

/-- The three-core commutator lies in the original scalar denominator. -/
theorem special_core_commutator_scalar (hc : Nat.card F = 2^2)
    (hconj : ∀ x, J.conj x = x^2) :
    commutator (pCore 3 J.specialSubgroup) ≤ (specialCoreProjection J).ker := by
  let : IsMulCommutative (pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    (projective_core_structure J hc hconj).2.1.toIsMulCommutative
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  change specialCoreProjection J (x*y*x⁻¹*y⁻¹) = 1
  rw [map_mul,map_mul,map_mul,map_inv,map_inv]
  have hcomm := (projective_core_structure J hc hconj).2.1.toIsMulCommutative
  have he : specialCoreProjection J x * specialCoreProjection J y =
      specialCoreProjection J y * specialCoreProjection J x := hcomm.is_comm.comm _ _
  rw [he,mul_inv_cancel_right,mul_inv_cancel]

/-- Every cube in the three-core lies in the same scalar denominator. -/
theorem special_core_cube_scalar (hc : Nat.card F = 2^2)
    (hconj : ∀ x, J.conj x = x^2) (x : pCore 3 J.specialSubgroup) :
    x^3 ∈ (specialCoreProjection J).ker := by
  change specialCoreProjection J (x^3) = 1
  rw [map_pow]
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    ((projective_core_structure J hc hconj).2.1.exponent_dvd_p) _
end BenderSuzuki.MatrixGroups.HermitianForm.SmallThreeCore
