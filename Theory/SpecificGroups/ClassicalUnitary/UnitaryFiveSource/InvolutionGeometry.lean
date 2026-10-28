module
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicTransitivity
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTwoLocal
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourRadicalCentralizers.Reduction
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.PlaneCenter
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Kernel

/-!
# Involution displacement geometry in PSU₅(4)

The image of `u - 1` for an involutory unitary matrix is totally isotropic.
A nonidentity matrix therefore has displacement rank one or two. The existing
SU transitivity moves this image to the standard line or plane. Self-adjointness
of `u - 1` shows that the transported matrix fixes the standard plane pointwise;
its exact plane-radical parameters have zero vector coordinate and are central.
Thus every native projective involution is conjugate into that center.

A projective involution lifts by taking the fifth power of an SU preimage:
the actual scalar kernel has order five. Projective commutation lifts by the
coprime four/five argument, so its full native centralizer preserves the same
displacement space. No assertion about outer involutions or ambient fusion is
made here. The ChapterF and Chapter6 companions use these actual parameters
and conjugating elements on the published marking.

Source: Aschbacher–Smith F.4.27(3–4), F.4.35 and F.4.42, printed pp.288,292,295.
-/

@[expose] public noncomputable section
open BenderSuzuki.MatrixGroups Matrix Subgroup
namespace Theory.SpecificGroups.UnitaryFive.InvolutionGeometry
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

def displacement (a : J.specialSubgroup) : Submodule F (Fin 5 → F) :=
  LinearMap.range ((linearAction J a).toLinearMap - LinearMap.id)

omit [CharP F 2] in
private theorem action_sq (a : J.specialSubgroup) (ha : a ^ 2 = 1) (v : Fin 5 → F) :
    linearAction J a (linearAction J a v) = v := by
  have hh := congrArg (fun g => linearAction J g v) ha
  simpa [pow_two] using hh

omit [CharP F 2] in
private theorem action_injective : Function.Injective (linearAction J) := by
  intro a b h
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.toLin.injective
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 5 → F)).injective
  exact h

omit [CharP F 2] in
theorem displacement_ne_bot (a : J.specialSubgroup) (ha : a ≠ 1) :
    displacement J a ≠ ⊥ := by
  intro hh
  apply ha
  apply action_injective J
  ext v : 1
  have hv : linearAction J a v - v ∈ displacement J a := ⟨v,rfl⟩
  rw [hh,Submodule.mem_bot] at hv
  simpa using sub_eq_zero.mp hv

theorem displacement_isotropic (hJ : J.form = 1)
    (a : J.specialSubgroup) (ha : a ^ 2 = 1) :
    displacement J a ≤ IsotropicGeometry.orthogonal J (displacement J a) := by
  rintro _ ⟨v,rfl⟩ _ ⟨w,rfl⟩
  have h1 := IsotropicGeometry.pairing_action J hJ a w v
  have h2 := IsotropicGeometry.pairing_action J hJ a w (linearAction J a v)
  rw [action_sq J a ha v] at h2
  change IsotropicGeometry.pairing J (linearAction J a w - w) (linearAction J a v - v) = 0
  change ((fun i => J.conj (linearAction J a w i - w i)) ⬝ᵥ
    (linearAction J a v - v)) = 0
  simp only [map_sub]
  rw [show (fun i => J.conj (linearAction J a w i) - J.conj (w i)) =
    (fun i => J.conj (linearAction J a w i)) - (fun i => J.conj (w i)) from rfl,
    sub_dotProduct,dotProduct_sub,dotProduct_sub]
  change (IsotropicGeometry.pairing J (linearAction J a w) (linearAction J a v) -
    IsotropicGeometry.pairing J (linearAction J a w) v) -
    (IsotropicGeometry.pairing J w (linearAction J a v) - IsotropicGeometry.pairing J w v) = 0
  rw [h1,h2]
  simp [CharTwo.sub_eq_add,add_comm]

theorem mem_displacement_shears (a : J.specialSubgroup) (ha : a ^ 2 = 1) :
    a ∈ shearSubgroup (linearAction J) (displacement J a) := by
  constructor
  · rintro _ ⟨v,rfl⟩
    change linearAction J a (linearAction J a v - v) = linearAction J a v - v
    rw [map_sub,action_sq J a ha]
    ext i
    simp [CharTwo.sub_eq_add,add_comm]
  · intro v
    exact ⟨v,rfl⟩

omit [CharP F 2] in
theorem centralizer_le_displacement_stabilizer [Finite F] (a : J.specialSubgroup) :
    centralizer ({a} : Set J.specialSubgroup) ≤ specialStabilizer J (displacement J a) := by
  intro b hb
  apply IsotropicGeometry.mem_specialStabilizer_of_preserves
  rintro _ ⟨v,rfl⟩
  refine ⟨linearAction J b v,?_⟩
  change linearAction J a (linearAction J b v) - linearAction J b v =
    linearAction J b (linearAction J a v - v)
  rw [map_sub]
  have he := congrArg (fun g => linearAction J g v) (mem_centralizer_singleton_iff.mp hb)
  simpa only [map_mul,LinearEquiv.mul_apply] using congrArg (fun x => x - linearAction J b v) he.symm

omit [CharP F 2] in
private theorem transport_shear (W : Submodule F (Fin 5 → F))
    (g a : J.specialSubgroup) (ha : a ∈ shearSubgroup (linearAction J)
      (W.map (linearAction J g).toLinearMap)) :
    g⁻¹ * a * g ∈ shearSubgroup (linearAction J) W := by
  constructor
  · intro v hv
    have hh := ha.1 (linearAction J g v) ⟨v,hv,rfl⟩
    simp only [map_mul,map_inv,LinearEquiv.mul_apply,LinearEquiv.coe_inv,hh,
      LinearEquiv.symm_apply_apply]
  · intro v
    obtain ⟨w,hw,he⟩ := ha.2 (linearAction J g v)
    have hh := congrArg (linearAction J g⁻¹) he
    have he' : linearAction J (g⁻¹ * a * g) v - v = w := by
      simpa only [map_mul,map_inv,LinearEquiv.mul_apply,LinearEquiv.coe_inv,map_sub,
        LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply] using hh.symm
    exact he' ▸ hw

theorem su_involution_placement [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (a : J.specialSubgroup) (ha : a ^ 2 = 1) (hne : a ≠ 1) :
    ∃ (b : Bool) (g : J.specialSubgroup),
      displacement J a = (if b then plane F else line F).map (linearAction J g).toLinearMap ∧
      g⁻¹ * a * g ∈ shearSubgroup (linearAction J) (if b then plane F else line F) := by
  obtain ⟨b,g,hg⟩ := IsotropicTransitivity.transitive J hcard hconj hJ
    (displacement J a) (displacement_ne_bot J a hne) (displacement_isotropic J hJ a ha)
  exact ⟨b,g,hg,transport_shear J _ g a (hg ▸ mem_displacement_shears J a ha)⟩

omit [CharP F 2] in
theorem projective_involution_lift [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4)
    (u : ProjectiveSpecialUnitaryMatrixGroup J) (hu : u ^ 2 = 1) :
    ∃ a : J.specialSubgroup, a ^ 2 = 1 ∧ project J a = u := by
  let : Finite (GL (Fin 5) F) := Finite.of_injective Units.val Units.val_injective
  obtain ⟨A,rfl⟩ := project_surjective J u
  have hker : A ^ 2 ∈ (project J).ker := by simpa only [MonoidHom.mem_ker,map_pow] using hu
  have hpow : (A ^ 2) ^ 5 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨A ^ 2,hker⟩ : (project J).ker))
    rw [card_project_kernel J hconj hcard] at hh
    exact congrArg Subtype.val hh
  refine ⟨A ^ 5,by simpa only [←pow_mul] using hpow,?_⟩
  rw [map_pow]
  calc
    project J A ^ 5 = (project J A ^ 2) ^ 2 * project J A := by group
    _ = project J A := by rw [hu]; simp

omit [CharP F 2] in
private theorem fixes_of_orthogonal_displacement (hJ : J.form = 1)
    (a : J.specialSubgroup) (ha : a ^ 2 = 1) (v : Fin 5 → F)
    (hv : v ∈ IsotropicGeometry.orthogonal J (displacement J a)) :
    linearAction J a v = v := by
  apply sub_eq_zero.mp
  apply dotProduct_eq_zero
  intro w
  let w' : Fin 5 → F := fun i => J.conj (w i)
  have hh := hv (linearAction J a w' - w') ⟨w',rfl⟩
  have he := IsotropicGeometry.pairing_action J hJ a w' (linearAction J a v)
  rw [action_sq J a ha] at he
  have hs : IsotropicGeometry.pairing J (linearAction J a w' - w') v =
      IsotropicGeometry.pairing J (linearAction J a w') v -
        IsotropicGeometry.pairing J w' v := by
    simp only [IsotropicGeometry.pairing,Pi.sub_apply,map_sub]
    exact sub_dotProduct _ _ _
  rw [hs,he] at hh
  have hh' : IsotropicGeometry.pairing J w' (linearAction J a v - v) = 0 := by
    simpa only [IsotropicGeometry.pairing,dotProduct_sub] using hh
  change (fun i => J.conj (J.conj (w i))) ⬝ᵥ (linearAction J a v - v) = 0 at hh'
  rw [show (fun i => J.conj (J.conj (w i))) = w from funext fun i => J.conj_involutive (w i)] at hh'
  simpa only [dotProduct_comm] using hh'

private theorem fixes_plane_of_displacements (hJ : J.form = 1)
    (a : J.specialSubgroup) (ha : a ^ 2 = 1)
    (hd : ∀ v, linearAction J a v - v ∈ plane F) :
    ∀ v : plane F, linearAction J a v.val = v.val := by
  intro v
  apply fixes_of_orthogonal_displacement J hJ a ha
  rintro _ ⟨w,rfl⟩
  exact plane_isotropic F J.conj ⟨_,hd w⟩ v

/-- Every native involution is conjugate to a central plane-radical parameter.
The conjugating element is in the actual SU group, before projectivization. -/
theorem projective_involution_to_plane_center [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (u : ProjectiveSpecialUnitaryMatrixGroup J) (hu : u ^ 2 = 1) (hne : u ≠ 1) :
    ∃ (g : J.specialSubgroup) (v : PlaneCore.Parameters J),
      v.x = 0 ∧ v ≠ 1 ∧
      (project J g)⁻¹ * u * project J g = (PlaneCore.Parameters.toParabolic hJ v).val := by
  obtain ⟨a,ha,he⟩ := projective_involution_lift J hcard hconj u hu
  have hane : a ≠ 1 := fun hh => hne (he.symm.trans (by rw [hh,map_one]))
  obtain ⟨b,g,_,hg⟩ := su_involution_placement J hcard hconj hJ a ha hane
  have hasq : (g⁻¹*a*g) ^ 2 = 1 := by
    have hh := congrArg (MulAut.conj g⁻¹) ha
    simpa only [map_pow,map_one,MulAut.conj_apply,inv_inv] using hh
  have hdisp : ∀ w, linearAction J (g⁻¹*a*g) w - w ∈ plane F := by
    intro w
    have hh := hg.2 w
    cases b
    · exact line_le_plane F hh
    · exact hh
  obtain ⟨v,hv⟩ := PlaneCore.exists_parameters_of_fixes_plane J hJ (g⁻¹*a*g)
    (fixes_plane_of_displacements J hJ _ hasq hdisp)
  have hv2 : v ^ 2 = 1 := by
    apply PlaneCore.Parameters.ambientGL_injective
    have hh := congrArg Subtype.val (hv ▸ hasq)
    change (PlaneCore.Parameters.ambientGL v) ^ 2 = 1 at hh
    simpa only [map_pow,map_one] using hh
  have hproj : (project J g)⁻¹ * u * project J g =
      (PlaneCore.Parameters.toParabolic hJ v).val := by
    rw [←he,←map_inv,←map_mul,←map_mul,←hv]
    rfl
  refine ⟨g,v,(PlaneCore.Parameters.square_eq_one_iff J v).mp hv2,?_,hproj⟩
  intro hv1
  have hh : (project J g)⁻¹ * u * project J g = 1 := by rw [hproj,hv1,map_one]; rfl
  apply hne
  have hh' := congrArg (MulAut.conj (project J g)) hh
  simpa [MulAut.conj_apply,mul_assoc] using hh'

omit [CharP F 2] in
/-- Native projective commutation preserves the SU displacement space.
The coprime four/five argument retains the nontrivial projective kernel. -/
theorem projective_centralizer_le_displacement [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4)
    (a : J.specialSubgroup) (ha : a ^ 2 = 1) :
    centralizer ({project J a} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      parabolic J (displacement J a) := by
  intro x hx
  obtain ⟨b,rfl⟩ := project_surjective J x
  have hfour : a ^ 4 = 1 := by rw [show 4 = 2*2 by decide,pow_mul,ha,one_pow]
  have hb := RadicalCentralizers.commute_of_project_commute_fourth_power J hconj hcard
    (mem_centralizer_singleton_iff.mp hx) hfour
  exact ⟨b,centralizer_le_displacement_stabilizer J a
    (mem_centralizer_singleton_iff.mpr hb),rfl⟩

end Theory.SpecificGroups.UnitaryFive.InvolutionGeometry
