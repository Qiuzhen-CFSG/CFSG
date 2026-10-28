module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveFlagAutomorphisms.QuotientAction
public import Theory.SpecificGroups.SL2.EvenBorelResidual.Semilinear

/-!
# Normalizing the quotient action with a marked native Levi element

The full flag fixes its intrinsic two-core. The literal plane-residual
quotient sends this same subgroup to the standard upper root of PSL₂(16).
Semilinear coverage therefore has its inner factor in the actual Borel.
Lift that factor through the plane SL₂ Levi; the upper-triangular condition
is exactly preservation of the marked line, so this lift preserves both
endpoints. Removing its inner action leaves the specified field action on
the quotient. The remaining actor's involution constraint is a cocycle
equation, and is not replaced by an involution assumption.

Source: the local normalization for Aschbacher–Smith F.4.29(2), printed
p.289 of refs/quasithin.pdf. The plane-radical and opposite-endpoint rigidity
needed to represent the whole remaining actor is a separate obligation.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryFiveFlagAutomorphisms
open Subgroup GreenBook.UnitaryFive
open Matrix.ProjectiveSpecialLinearGroup
variable (U : Model 4)

/-- The canonical quotient map in the fixed PSL₂ coordinates. -/
def rightQuotientProjection : U.rightLocalImage →* Theory.PSL2.Group U.F :=
  U.rightLocalImageQuotientEquiv.toMonoidHom.comp (QuotientGroup.mk' _)

@[simp] theorem rightQuotientProjection_equiv (x : U.rightLocal) :
    rightQuotientProjection U (U.rightLocalImageEquiv x) =
      Theory.PSL2.quotientMap U.F (U.rightLocalProjection x) :=
  U.rightLocalImageQuotientEquiv_mk x

theorem rightQuotientProjection_action (a : flagAutomorphisms U) (x : U.rightLocalImage) :
    rightQuotientProjection U (rightLocalAction U a x) =
      rightLinearAction U a (rightQuotientProjection U x) := by
  change U.rightLocalImageQuotientEquiv (QuotientGroup.mk' _ (rightLocalAction U a x)) =
    U.rightLocalImageQuotientEquiv (rightQuotientAction U a
      (U.rightLocalImageQuotientEquiv.symm
        (U.rightLocalImageQuotientEquiv (QuotientGroup.mk' _ x))))
  rw [MulEquiv.symm_apply_apply,rightQuotientAction_mk]

/-- Both endpoint stabilizers preserve the intrinsic two-core of the flag. -/
theorem flagTwoSubgroup_preserved (a : flagAutomorphisms U) :
    U.flagTwoSubgroup.map a.val.toMonoidHom = U.flagTwoSubgroup := by
  have ho : U.overlap.map a.val.toMonoidHom = U.overlap := by
    change (U.leftParabolic ⊓ U.rightParabolic).map a.val.toMonoidHom = _
    rw [Subgroup.map_inf _ _ _ a.val.injective]
    exact congrArg₂ (· ⊓ ·)
      (show U.leftParabolic.map a.val.toMonoidHom = U.leftParabolic from a.property.1)
      (show U.rightParabolic.map a.val.toMonoidHom = U.rightParabolic from a.property.2)
  rw [←U.overlap_pCore_map]
  change (U.overlap.pCoreIn 2).map a.val.toMonoidHom = U.overlap.pCoreIn 2
  rw [map_pCoreIn_of_injective 2 _ _ a.val.injective,ho]

theorem rightFlagSylow_preserved (a : flagAutomorphisms U) :
    (U.flagTwoSubgroup.subgroupOf U.rightLocalImage).map
      (rightLocalAction U a).toMonoidHom = U.flagTwoSubgroup.subgroupOf U.rightLocalImage := by
  apply Subgroup.map_injective (f := U.rightLocalImage.subtype) Subtype.val_injective
  rw [Subgroup.map_map]
  have he : U.rightLocalImage.subtype.comp (rightLocalAction U a).toMonoidHom =
      a.val.toMonoidHom.comp U.rightLocalImage.subtype := by
    apply MonoidHom.ext
    intro x
    exact rightLocalAction_val U a x
  rw [he,←Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le U.flagTwoSubgroup_le_rightLocalImage,
    flagTwoSubgroup_preserved]

/-- The image is the standard upper root, with the actual residual marking. -/
theorem rightFlagSylow_quotient :
    (U.flagTwoSubgroup.subgroupOf U.rightLocalImage).map (rightQuotientProjection U) =
      OddBorel.kernel U.F := by
  have hS : U.flagTwoSubgroup.subgroupOf U.rightLocalImage =
      (U.rightLocalImageSylow : Subgroup U.rightLocalImage) := by
    apply Subgroup.map_injective (f := U.rightLocalImage.subtype) Subtype.val_injective
    rw [Subgroup.map_subgroupOf_eq_of_le U.flagTwoSubgroup_le_rightLocalImage,
      U.rightLocalImageSylow_map]
  rw [hS]
  change ((U.rightLocalSylow : Subgroup U.rightLocal).map
    U.rightLocalImageEquiv.toMonoidHom).map (rightQuotientProjection U) = _
  rw [Subgroup.map_map]
  have he : (rightQuotientProjection U).comp U.rightLocalImageEquiv.toMonoidHom =
      (Theory.PSL2.quotientMap U.F).comp U.rightLocalProjection := by
    ext x
    exact rightQuotientProjection_equiv U x
  rw [he,←Subgroup.map_map]
  change (((Matrix.SpecialLinearGroup.upperUnipotent U.F).comap
    U.rightLocalProjection).map U.rightLocalProjection).map _ = _
  rw [Subgroup.map_comap_eq_self_of_surjective U.rightLocalProjection_surjective]
  exact EvenBorelResidual.upperUnipotent_map U.F

/-- The induced PSL₂ actor preserves the standard upper root, not merely
an unspecified conjugate Sylow subgroup. -/
theorem rightLinearAction_preserves_root (a : flagAutomorphisms U) :
    (OddBorel.kernel U.F).map (rightLinearAction U a).toMonoidHom = OddBorel.kernel U.F := by
  rw [←rightFlagSylow_quotient U,Subgroup.map_map]
  have he : (rightLinearAction U a).toMonoidHom.comp (rightQuotientProjection U) =
      (rightQuotientProjection U).comp (rightLocalAction U a).toMonoidHom := by
    ext x
    exact (rightQuotientProjection_action U a x).symm
  rw [he,←Subgroup.map_map,rightFlagSylow_preserved]

private theorem fieldAut_eq (σ : U.F ≃+* U.F) :
    Theory.PSL2.fieldAut σ = Atlas.fieldEquivPSL 2 σ := by
  ext x
  obtain ⟨g,rfl⟩ := Theory.PSL2.quotientMap_surjective U.F x
  rw [Theory.PSL2.fieldAut_apply_quotientMap]
  change _ = Atlas.fieldEquivPSL 2 σ (QuotientGroup.mk' _ g)
  rw [Atlas.fieldEquivPSL_mk]
  rfl

/-- Semilinear coverage with an inner factor in the marked Borel. This is
a quotient normalization only; lifting it to a unitary flag matrix is separate. -/
theorem rightLinearAction_semilinear_borel (a : flagAutomorphisms U) :
    ∃ g : Theory.PSL2.Group U.F, g ∈ OddBorel.borel U.F ∧
      rightLinearAction U a = MulAut.conj g * Theory.PSL2.fieldAut (rightCoefficient U a) := by
  obtain ⟨g,σ,he⟩ := Theory.PSL2.semilinear_coverage (rightLinearAction U a)
  have hc : rightCoefficient U a = σ := by
    change Theory.PSL2.fieldProjection U.F (rightLinearAction U a) = σ
    rw [he,map_mul,Theory.PSL2.fieldProjection_fieldAut]
    have hg : Theory.PSL2.fieldProjection U.F (MulAut.conj g) = 1 := by
      change MulAut.conj g ∈ (Theory.PSL2.fieldProjection U.F).ker
      rw [Theory.PSL2.fieldProjection_ker]
      exact ⟨g,rfl⟩
    rw [hg,one_mul]
  have hr := rightLinearAction_preserves_root U a
  rw [he,fieldAut_eq U σ] at hr
  exact ⟨g,EvenBorelResidual.Semilinear.inner_factor_mem_borel U.F g σ hr, hc.symm ▸ he⟩



/-- Conjugation by the full native middle, with the native flag retained. -/
def innerFlag : U.overlap →* flagAutomorphisms U :=
  Theory.SpecificGroups.ClassicalUnitary.NativeAmalgamActions.innerMiddle
    U.leftParabolic U.rightParabolic U.overlap inf_le_left inf_le_right

/-- A Borel element lifts through the actual plane SL₂ Levi into the flag. -/
theorem exists_rightBorelLift (g : OddBorel.borel U.F) :
    ∃ u : U.rightLocalImage, u.val ∈ U.overlap ∧ rightQuotientProjection U u = g.val := by
  obtain ⟨A,hA⟩ := (EvenBorelResidual.rankOneBorelEquiv U.F).surjective g
  have hq : Theory.PSL2.quotientMap U.F A.val = g.val := congrArg Subtype.val hA
  let u := U.rightLocalImageEquiv (U.rightLocalEquiv (SemidirectProduct.inr A.val))
  have hv : u.val = (U.rightSLLevi A.val).val := by
    dsimp only [u]
    rw [U.rightLocalImageEquiv_val,U.rightLocalEquiv_val]
    simp
  refine ⟨u,?_,?_⟩
  · change u.val ∈ U.leftParabolic ∧ u.val ∈ U.rightParabolic
    rw [hv]
    refine ⟨?_,(U.rightSLLevi A.val).property⟩
    exact (Theory.SpecificGroups.UnitaryFive.Flag.planeSL_mem_line_iff
      U.form U.rightLeviTrace U.rightLeviTrace_spec U.matrix A.val).mpr
        ((Matrix.SpecialLinearGroup.mem_rankOneBorel_iff A.val).mp A.property)
  · change rightQuotientProjection U
      (U.rightLocalImageEquiv (U.rightLocalEquiv (SemidirectProduct.inr A.val))) = g.val
    rw [rightQuotientProjection_equiv,U.rightLocalProjection_equiv]
    exact hq

/-- On the residual the native inner lift has exactly the indicated quotient
conjugator. This checks the literal maps before normalizing the actor. -/
theorem rightLinearAction_innerFlag (u : U.rightLocalImage) (hu : u.val ∈ U.overlap) :
    rightLinearAction U (innerFlag U ⟨u.val,hu⟩) = MulAut.conj (rightQuotientProjection U u) := by
  have hq : Function.Surjective (rightQuotientProjection U) :=
    U.rightLocalImageQuotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  apply MulEquiv.ext
  intro y
  obtain ⟨x,rfl⟩ := hq y
  rw [←rightQuotientProjection_action]
  have hx : rightLocalAction U (innerFlag U ⟨u.val,hu⟩) x = u * x * u⁻¹ := by
    apply Subtype.ext
    exact rightLocalAction_val U (innerFlag U ⟨u.val,hu⟩) x
  rw [hx,map_mul,map_mul,map_inv]
  rfl

/-- Remove the quotient inner factor with a genuine flag-preserving native
Levi element. No involution equation for the remaining actor is asserted. -/
theorem rightLinearAction_normalize (a : flagAutomorphisms U) :
    ∃ (b : U.overlap) (β : flagAutomorphisms U),
      b.val ∈ U.rightLocalImage ∧ a = innerFlag U b * β ∧
      rightLinearAction U β = Theory.PSL2.fieldAut (rightCoefficient U a) := by
  obtain ⟨g,hg,he⟩ := rightLinearAction_semilinear_borel U a
  obtain ⟨u,hu,hq⟩ := exists_rightBorelLift U ⟨g,hg⟩
  let b : U.overlap := ⟨u.val,hu⟩
  let s := innerFlag U b
  have hs : rightLinearAction U s = MulAut.conj g :=
    (rightLinearAction_innerFlag U u hu).trans (congrArg MulAut.conj hq)
  refine ⟨b,s⁻¹*a,u.property,?_,?_⟩
  · exact (mul_inv_cancel_left s a).symm
  · rw [map_mul,map_inv,hs,he,inv_mul_cancel_left]

/-- A residual inner flag element has trivial field coefficient. -/
theorem rightCoefficient_innerFlag (u : U.rightLocalImage) (hu : u.val ∈ U.overlap) :
    rightCoefficient U (innerFlag U ⟨u.val,hu⟩) = 1 := by
  change Theory.PSL2.fieldProjection U.F (rightLinearAction U (innerFlag U ⟨u.val,hu⟩)) = 1
  rw [rightLinearAction_innerFlag]
  change MulAut.conj (rightQuotientProjection U u) ∈ (Theory.PSL2.fieldProjection U.F).ker
  rw [Theory.PSL2.fieldProjection_ker]
  exact ⟨rightQuotientProjection U u,rfl⟩

/-- Retain the exact constraint from the original involution equation after
removing the matching native quotient conjugator. -/
theorem rightLinearAction_normalize_involution (a : flagAutomorphisms U) (ha : a ^ 2 = 1) :
    ∃ (b : U.overlap) (β : flagAutomorphisms U),
      b.val ∈ U.rightLocalImage ∧ a = innerFlag U b * β ∧
      rightLinearAction U β = Theory.PSL2.fieldAut (rightCoefficient U a) ∧
      β * innerFlag U b * β = (innerFlag U b)⁻¹ := by
  obtain ⟨b,β,hb,he,hq⟩ := rightLinearAction_normalize U a
  refine ⟨b,β,hb,he,hq,?_⟩
  apply eq_inv_of_mul_eq_one_right
  simpa only [he,pow_two,mul_assoc] using ha

end CFSG.Quasithin.ChapterF.UnitaryFiveFlagAutomorphisms
