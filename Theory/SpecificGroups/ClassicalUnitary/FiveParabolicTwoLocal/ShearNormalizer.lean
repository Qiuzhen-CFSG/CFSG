module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineShears
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourScalarKernel
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicGeometry

/-!
# Normalizers of projective unitary shears

A shear fixes a subspace pointwise and has every displacement in that
subspace. In characteristic two these elements square to one. The subspace
stabilizer normalizes the entire shear subgroup. Conversely, if every vector
of the subspace is a shear displacement, its normalizer preserves the subspace.

This argument descends to the actual projective unitary group: two elements
whose squares are one and whose projective images agree differ by a central
scalar whose square is one. In characteristic two that scalar is one. Thus
normalizing the projective shear subgroup also normalizes its SU lift.

The result applies to the isotropic line and plane parabolics without any
assumption on their full unipotent radicals. Source: the defining-characteristic
parabolic construction used in Aschbacher--Smith, *The Classification of
Quasithin Groups*, F.1.12(7), printed pp.263--264.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
private theorem linearAction_injective (J : HermitianForm 5 F) :
    Function.Injective (linearAction J) := by
  intro a b h
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.toLin.injective
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 5 → F)).injective
  exact h

private theorem kernel_sq_one (J : HermitianForm 5 F) (a : J.specialSubgroup)
    (hk : a ∈ (project J).ker) (hs : a ^ 2 = 1) : a = 1 := by
  have hk' : ProjGenLinGroup.mk a.val = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hk'
  obtain ⟨u, hu⟩ := hk'
  have hs' : (GeneralLinearGroup.scalar (Fin 5) u) ^ 2 = 1 := by
    rw [hu]
    exact congrArg Subtype.val hs
  rw [← map_pow] at hs'
  have he := congrArg (fun A : GL (Fin 5) F => (A : Matrix (Fin 5) (Fin 5) F) 0 0) hs'
  have hu2 : (u : F) ^ 2 = 1 := by
    change (u ^ 2 : Fˣ).val = 1 at he
    exact he
  have hu1 : (u : F) = 1 := by
    simpa only [CharTwo.neg_eq, or_self] using sq_eq_one_iff.mp hu2
  apply Subtype.ext
  rw [← hu, show u = 1 from Units.ext hu1, map_one]
  rfl

private theorem project_injective_on_involutions (J : HermitianForm 5 F)
    (a b : J.specialSubgroup) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (he : project J a = project J b) : a = b := by
  let z := a * b⁻¹
  have hk : z ∈ (project J).ker := by
    simp [z, MonoidHom.mem_ker, he]
  have hc : Commute z b := (Subgroup.mem_center_iff.mp (project_kernel_le_center J hk) b).symm
  have hz : z ^ 2 = 1 := by
    have h := hc.mul_pow 2
    have hzb : z * b = a := by simp [z]
    rw [hzb, ha, hb, mul_one] at h
    exact h.symm
  have hz1 := kernel_sq_one J z hk hz
  exact mul_inv_eq_one.mp hz1

private theorem shear_sq (J : HermitianForm 5 F) (W : Submodule F (Fin 5 → F))
    (a : J.specialSubgroup) (ha : a ∈ shearSubgroup (linearAction J) W) : a ^ 2 = 1 := by
  apply linearAction_injective J
  ext v : 1
  have h := ha.1 (linearAction J a v - v) (ha.2 v)
  rw [map_sub] at h
  have htwo (w : Fin 5 → F) : w + w = 0 := by ext i; exact CharTwo.add_self_eq_zero _
  have he : linearAction J a (linearAction J a v) = v := by
    have : linearAction J a (linearAction J a v) =
        (linearAction J a v - v) + linearAction J a v := (sub_eq_iff_eq_add).mp h
    rw [this]
    have : (linearAction J a v - v) + linearAction J a v =
        (linearAction J a v + linearAction J a v) - v := by abel
    rw [this, htwo, zero_sub]
    exact neg_eq_iff_add_eq_zero.mpr (htwo v)
  simpa [pow_two] using he

omit [CharP F 2] in
private theorem stabilizer_normalizes_shears (J : HermitianForm 5 F)
    (W : Submodule F (Fin 5 → F)) :
    specialStabilizer J W ≤
      Subgroup.normalizer (shearSubgroup (linearAction J) W : Set J.specialSubgroup) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg a ha
  have hg' := (mem_specialStabilizer_iff J W g).mp hg
  have hi := (mem_specialStabilizer_iff J W g⁻¹).mp ((specialStabilizer J W).inv_mem hg)
  change ∀ v, linearAction J g v ∈ W ↔ v ∈ W at hg'
  change ∀ v, linearAction J g⁻¹ v ∈ W ↔ v ∈ W at hi
  constructor
  · intro v hv
    simp only [map_mul, LinearEquiv.mul_apply]
    rw [ha.1 _ ((hi v).mpr hv)]
    simp
  · intro v
    have h := (hg' _).mpr (ha.2 (linearAction J g⁻¹ v))
    simpa using h

private theorem normalizes_shears_of_project (J : HermitianForm 5 F)
    (W : Submodule F (Fin 5 → F)) (g : J.specialSubgroup)
    (hg : project J g ∈ Subgroup.normalizer
      ((shearSubgroup (linearAction J) W).map (project J) :
        Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    g ∈ Subgroup.normalizer (shearSubgroup (linearAction J) W : Set J.specialSubgroup) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have hm := (Subgroup.mem_normalizer_iff.mp hg (project J a)).mp
      (show project J a ∈ (shearSubgroup (linearAction J) W).map (project J) from ⟨a, ha, rfl⟩)
    obtain ⟨b, hb, he⟩ := hm
    have hsq : (g * a * g⁻¹) ^ 2 = 1 := by
      simpa only [MulAut.conj_apply, map_one] using
        (map_pow (MulAut.conj g) a 2).symm.trans (congrArg (MulAut.conj g) (shear_sq J W a ha))
    have hbe : b = g * a * g⁻¹ := project_injective_on_involutions J b _
      (shear_sq J W b hb) hsq (by simpa only [map_mul, map_inv] using he)
    rwa [← hbe]
  · intro ha
    have hg' := (Subgroup.normalizer
      ((shearSubgroup (linearAction J) W).map (project J) :
        Set (ProjectiveSpecialUnitaryMatrixGroup J))).inv_mem hg
    have hm := (Subgroup.mem_normalizer_iff.mp hg' (project J (g * a * g⁻¹))).mp
      (show project J (g * a * g⁻¹) ∈ (shearSubgroup (linearAction J) W).map (project J) from
        ⟨_, ha, rfl⟩)
    have hm' : project J a ∈ (shearSubgroup (linearAction J) W).map (project J) := by
      simpa [map_mul, map_inv, mul_assoc] using hm
    obtain ⟨b, hb, he⟩ := hm'
    have hsq : a ^ 2 = 1 := by
      have hh := congrArg (MulAut.conj g⁻¹) (shear_sq J W _ ha)
      simpa [map_pow, MulAut.conj_apply, mul_assoc] using hh
    rwa [← project_injective_on_involutions J b a (shear_sq J W b hb) hsq he]

/-- The shear subgroup in the ambient projective group. -/
def projectiveShearSubgroup (J : HermitianForm 5 F) (W : Submodule F (Fin 5 → F)) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (shearSubgroup (linearAction J) W).map (project J)

/-- Projective shears form a two-group. -/
theorem projectiveShearSubgroup_isPGroup (J : HermitianForm 5 F)
    (W : Submodule F (Fin 5 → F)) : IsPGroup 2 (projectiveShearSubgroup J W) :=
  (shearSubgroup_isPGroup _ (linearAction_injective J) W).map (project J)

/-- If shear displacements fill the subspace, its full projective stabilizer
is exactly the ambient normalizer of the projective shear subgroup. -/
theorem normalizer_projectiveShearSubgroup [Finite F] (J : HermitianForm 5 F)
    (W : Submodule F (Fin 5 → F))
    (hgen : ∀ v ∈ W, ∃ a ∈ shearSubgroup (linearAction J) W,
      ∃ w, linearAction J a w - w = v) :
    Subgroup.normalizer (projectiveShearSubgroup J W : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      parabolic J W := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := project_surjective J x
    have hg := normalizes_shears_of_project J W g hx
    refine ⟨g, ?_, rfl⟩
    apply IsotropicGeometry.mem_specialStabilizer_of_preserves
    intro v hv
    obtain ⟨a, ha, w, rfl⟩ := hgen v hv
    have hc := (Subgroup.mem_normalizer_iff.mp hg a).mp ha
    have hd := hc.2 (linearAction J g w)
    simpa only [map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply, map_sub] using hd
  · exact (Subgroup.map_mono (stabilizer_normalizes_shears J W)).trans
      ((shearSubgroup (linearAction J) W).le_normalizer_map (project J))

end Theory.SpecificGroups.UnitaryFive
