module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineShears
public import Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
public import Theory.GroupTheory.QuasithinBasic

/-!
# Projective shear normalizers in arbitrary unitary dimension

The subspace stabilizer normalizes its pointwise shears. When their displacements
fill the subspace, it is exactly their normalizer, also after the literal map to
PGL: a central scalar of square one is trivial in characteristic two.
This extends the five-dimensional calculation without altering its public API.
The isotropic-line application is the parabolic needed in Aschbacher--Smith
A.2.18, printed p.40 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open BenderSuzuki.MatrixGroups Matrix
open scoped Pointwise
namespace Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections
open ProjectiveKernel
open Theory.SpecificGroups.UnitaryFive (shearSubgroup shearSubgroup_isPGroup)
variable {F : Type*} [Field F] {d : ℕ} [NeZero d]

/-- The natural matrix action of SU on the vector space. -/
def linearAction (J : HermitianForm d F) : J.specialSubgroup →*
    ((Fin d → F) ≃ₗ[F] (Fin d → F)) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin d → F)).toMonoidHom.comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom).comp J.specialSubgroup.subtype

/-- Exact stabilizer of a subspace inside the special unitary group. -/
def specialStabilizer (J : HermitianForm d F) (W : Submodule F (Fin d → F)) :
    Subgroup J.specialSubgroup :=
  (MulAction.stabilizer ((Fin d → F) ≃ₗ[F] (Fin d → F)) W).comap (linearAction J)

omit [NeZero d] in
/-- Stabilizer membership is the usual preservation condition on matrix vectors. -/
theorem mem_specialStabilizer_iff (J : HermitianForm d F)
    (W : Submodule F (Fin d → F)) (A : J.specialSubgroup) :
    A ∈ specialStabilizer J W ↔
      ∀ v, (A.val : Matrix (Fin d) (Fin d) F) *ᵥ v ∈ W ↔ v ∈ W := by
  change linearAction J A ∈ MulAction.stabilizer _ W ↔ _
  rw [Submodule.stabilizer_coe, MulAction.mem_stabilizer_set]
  rfl

/-- Projective image of a subspace stabilizer; isotropic lines and planes give parabolics. -/
def parabolic (J : HermitianForm d F) (W : Submodule F (Fin d → F)) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (specialStabilizer J W).map (project J)

omit [NeZero d] in
theorem mem_specialStabilizer_of_preserves [Finite F]
    (J : HermitianForm d F) (W : Submodule F (Fin d → F)) (g : J.specialSubgroup)
    (h : ∀ v ∈ W, linearAction J g v ∈ W) : g ∈ specialStabilizer J W := by
  change linearAction J g ∈ MulAction.stabilizer _ W
  rw [Submodule.stabilizer_coe, MulAction.mem_stabilizer_set_iff_smul_set_subset
    (Set.toFinite (W : Set (Fin d → F)))]
  rintro _ ⟨v, hv, rfl⟩
  exact h v hv

variable [CharP F 2]

omit [CharP F 2] [NeZero d] in
private theorem linearAction_injective (J : HermitianForm d F) :
    Function.Injective (linearAction J) := by
  intro a b h
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.toLin.injective
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin d → F)).injective
  exact h

private theorem kernel_sq_one (J : HermitianForm d F) (a : J.specialSubgroup)
    (hk : a ∈ (project J).ker) (hs : a ^ 2 = 1) : a = 1 := by
  have hk' : ProjGenLinGroup.mk a.val = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hk'
  obtain ⟨u, hu⟩ := hk'
  have hs' : (GeneralLinearGroup.scalar (Fin d) u) ^ 2 = 1 := by
    rw [hu]
    exact congrArg Subtype.val hs
  rw [← map_pow] at hs'
  have he := congrArg (fun A : GL (Fin d) F => (A : Matrix (Fin d) (Fin d) F) 0 0) hs'
  have hu2 : (u : F) ^ 2 = 1 := by
    change (u ^ 2 : Fˣ).val = 1 at he
    exact he
  have hu1 : (u : F) = 1 := by
    simpa only [CharTwo.neg_eq, or_self] using sq_eq_one_iff.mp hu2
  apply Subtype.ext
  rw [← hu, show u = 1 from Units.ext hu1, map_one]
  rfl

private theorem project_injective_on_involutions (J : HermitianForm d F)
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

omit [NeZero d] in
private theorem shear_sq (J : HermitianForm d F) (W : Submodule F (Fin d → F))
    (a : J.specialSubgroup) (ha : a ∈ shearSubgroup (linearAction J) W) : a ^ 2 = 1 := by
  apply linearAction_injective J
  ext v : 1
  have h := ha.1 (linearAction J a v - v) (ha.2 v)
  rw [map_sub] at h
  have htwo (w : Fin d → F) : w + w = 0 := by ext i; exact CharTwo.add_self_eq_zero _
  have he : linearAction J a (linearAction J a v) = v := by
    have : linearAction J a (linearAction J a v) =
        (linearAction J a v - v) + linearAction J a v := (sub_eq_iff_eq_add).mp h
    rw [this]
    have : (linearAction J a v - v) + linearAction J a v =
        (linearAction J a v + linearAction J a v) - v := by abel
    rw [this, htwo, zero_sub]
    exact neg_eq_iff_add_eq_zero.mpr (htwo v)
  simpa [pow_two] using he

omit [CharP F 2] [NeZero d] in
private theorem stabilizer_normalizes_shears (J : HermitianForm d F)
    (W : Submodule F (Fin d → F)) :
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

private theorem normalizes_shears_of_project (J : HermitianForm d F)
    (W : Submodule F (Fin d → F)) (g : J.specialSubgroup)
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
def projectiveShearSubgroup (J : HermitianForm d F) (W : Submodule F (Fin d → F)) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (shearSubgroup (linearAction J) W).map (project J)

omit [NeZero d] in
/-- Projective shears form a two-group. -/
theorem projectiveShearSubgroup_isPGroup (J : HermitianForm d F)
    (W : Submodule F (Fin d → F)) : IsPGroup 2 (projectiveShearSubgroup J W) :=
  (shearSubgroup_isPGroup _ (linearAction_injective J) W).map (project J)

/-- If shear displacements fill the subspace, its full projective stabilizer
is exactly the ambient normalizer of the projective shear subgroup. -/
theorem normalizer_projectiveShearSubgroup [Finite F] (J : HermitianForm d F)
    (W : Submodule F (Fin d → F))
    (hgen : ∀ v ∈ W, ∃ a ∈ shearSubgroup (linearAction J) W,
      ∃ w, linearAction J a w - w = v) :
    Subgroup.normalizer (projectiveShearSubgroup J W : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      parabolic J W := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := project_surjective J x
    have hg := normalizes_shears_of_project J W g hx
    refine ⟨g, ?_, rfl⟩
    apply mem_specialStabilizer_of_preserves
    intro v hv
    obtain ⟨a, ha, w, rfl⟩ := hgen v hv
    have hc := (Subgroup.mem_normalizer_iff.mp hg a).mp ha
    have hd := hc.2 (linearAction J g w)
    simpa only [map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply, map_sub] using hd
  · exact (Subgroup.map_mono (stabilizer_normalizes_shears J W)).trans
      ((shearSubgroup (linearAction J) W).le_normalizer_map (project J))

omit [CharP F 2] [NeZero d] in
/-- Scalar projective kernels preserve every vector subspace. -/
theorem project_kernel_le_stabilizer (J : HermitianForm d F)
    (W : Submodule F (Fin d → F)) : (project J).ker ≤ specialStabilizer J W := by
  intro a ha
  have hp : ProjGenLinGroup.mk a.val = 1 := congrArg Subtype.val ha
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hp
  obtain ⟨u, hu⟩ := hp
  rw [mem_specialStabilizer_iff]
  intro v
  rw [← hu]
  change Matrix.scalar (Fin d) (u : F) *ᵥ v ∈ W ↔ v ∈ W
  have he : Matrix.scalar (Fin d) (u : F) *ᵥ v = (u : F) • v := by
    ext i
    simp [Matrix.scalar, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [he]
  exact Submodule.smul_mem_iff W (Units.ne_zero u)

omit [CharP F 2] [NeZero d] in
/-- Membership in the projective stabilizer can be tested on the given SU lift. -/
theorem project_mem_parabolic_iff (J : HermitianForm d F)
    (W : Submodule F (Fin d → F)) (a : J.specialSubgroup) :
    project J a ∈ parabolic J W ↔ a ∈ specialStabilizer J W := by
  constructor
  · rintro ⟨b, hb, he⟩
    have hz : b⁻¹ * a ∈ (project J).ker := by
      simp [MonoidHom.mem_ker, he]
    have hm := (specialStabilizer J W).mul_mem hb (project_kernel_le_stabilizer J W hz)
    simpa using hm
  · intro ha
    exact ⟨a, ha, rfl⟩

end Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections
