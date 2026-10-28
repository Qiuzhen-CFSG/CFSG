module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveFlagAutomorphisms.Representation
public import Theory.SpecificGroups.SL2.EvenBorelResidual.Semilinear
public import Theory.FieldTheory.BinaryTorusTwoPower
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Detecting the original U₅ field and odd scalar extension

The line residual has index three in the full native overlap. Its normalized
Borel displacements therefore fix the three-residual of the plane quotient's
multiplicative torus. Since the field has order sixteen, a two-power field
coefficient fixing that torus is trivial. This uses the literal residual
quotient map and its specified upper root, retaining all odd overlap elements.

A flag actor with trivial plane coefficient is an inner flag correction times
one native scalar actor. The scalar group has order fifteen, so a two-element
of this kernel is inner on the whole projective carrier. No involution-only
representation or faithful special-to-projective map is substituted here.
`UnitaryFive` applies these calculations to every original selected perfect R.

Source: Aschbacher--Smith F.1.12, printed pp.263--264, and the native flag
rigidity used in F.4.29(2), p.289 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace OriginalUnitaryFive
open ChapterF.GreenBook.UnitaryFive
open ChapterF.UnitaryFiveFlagAutomorphisms
variable (M : Model 4)

private theorem line_residual_contains_threeResidual :
    pResidual 3 M.overlap ≤ M.leftLocalImage.subgroupOf M.overlap := by
  let := M.leftLocalImage_normal_in_overlap
  apply (pResidual_le_iff_isPGroup_quotient 3 _).mpr
  apply IsPGroup.of_card (n := 1)
  rw [← index_eq_card, M.leftLocalImage_overlap_index, pow_one]

private theorem plane_borel_quotient :
    (M.overlap.subgroupOf M.rightLocalImage).map (rightQuotientProjection M) =
      Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel M.F := by
  have hN : normalizer (M.rightLocalImageSylow : Set M.rightLocalImage) =
      M.overlap.subgroupOf M.rightLocalImage := by
    apply Subgroup.map_injective M.rightLocalImage.subtype_injective
    have hb := M.source_borel_right
    rw [M.rightSylowNormalizerImage_eq] at hb
    rw [subgroupOf_map_subtype]
    have hU : (M.rightLocalImageSylow : Subgroup M.rightLocalImage) =
        M.flagTwoSubgroup.subgroupOf M.rightLocalImage := by
      apply Subgroup.map_injective M.rightLocalImage.subtype_injective
      rw [M.rightLocalImageSylow_map,map_subgroupOf_eq_of_le M.flagTwoSubgroup_le_rightLocalImage]
    change (normalizer ((M.rightLocalImageSylow : Subgroup M.rightLocalImage) : Set M.rightLocalImage)).map _ = _
    rw [hU,←subgroupOf_normalizer_eq M.flagTwoSubgroup_le_rightLocalImage,subgroupOf_map_subtype]
    simpa only [ChapterF.Source.borel,inf_of_le_left M.flagTwoSubgroup_le_rightLocalImage,inf_comm] using hb
  have hsurj : Function.Surjective (rightQuotientProjection M) :=
    M.rightLocalImageQuotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  rw [←hN,M.rightLocalImageSylow.normalizer_map_surjective _ hsurj]
  have hU : (M.rightLocalImageSylow : Subgroup M.rightLocalImage) =
      M.flagTwoSubgroup.subgroupOf M.rightLocalImage := by
    apply Subgroup.map_injective M.rightLocalImage.subtype_injective
    rw [M.rightLocalImageSylow_map,map_subgroupOf_eq_of_le M.flagTwoSubgroup_le_rightLocalImage]
  rw [hU,rightFlagSylow_quotient]
  exact Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.normalizer_kernel M.F


private theorem fieldAut_eq (σ : M.F ≃+* M.F) :
    Theory.PSL2.fieldAut σ = Atlas.fieldEquivPSL 2 σ := by
  ext x
  obtain ⟨g,rfl⟩ := Theory.PSL2.quotientMap_surjective M.F x
  rw [Theory.PSL2.fieldAut_apply_quotientMap]
  change _ = Atlas.fieldEquivPSL 2 σ (QuotientGroup.mk' _ g)
  rw [Atlas.fieldEquivPSL_mk]
  rfl

/-- The line residual's index-three overlap detects all two-power field
coefficients of a flag actor whose displacements there lie in the native Sylow. -/
theorem coefficient_eq_one_of_line_borel_displacements
    (a : flagAutomorphisms M) (k : ℕ) (ha : a^(2^k)=1)
    (hd : ∀ x ∈ M.leftLocalImage ⊓ M.overlap,
      x⁻¹ * a.val x ∈ M.flagTwoSubgroup) : rightCoefficient M a = 1 := by
  let D := M.overlap.subgroupOf M.rightLocalImage
  let B := Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel M.F
  let f : D →* B :=
    (MulEquiv.subgroupCongr (plane_borel_quotient M)).toMonoidHom.comp
      ((rightQuotientProjection M).subgroupMap D)
  have f_val (y : D) : (f y).val = rightQuotientProjection M y.val := rfl
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr (plane_borel_quotient M)).surjective.comp
      (MonoidHom.subgroupMap_surjective _ _)
  let j : D →* M.overlap :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hdisp (x : B) (hx : x ∈ pResidual 3 B) :
      x.val⁻¹ * rightLinearAction M a x.val ∈
        Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel M.F := by
    rw [←map_pResidual_of_surjective 3 f hf] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    have hl : y.val.val ∈ M.leftLocalImage :=
      line_residual_contains_threeResidual M
        (map_pResidual_le 3 j (mem_map_of_mem j hy))
    have hh := hd y.val.val ⟨hl,y.property⟩
    have hq := mem_map_of_mem (rightQuotientProjection M)
      (show (y.val⁻¹ * rightLocalAction M a y.val) ∈
        M.flagTwoSubgroup.subgroupOf M.rightLocalImage from by
          change y.val.val⁻¹ * (rightLocalAction M a y.val).val ∈ M.flagTwoSubgroup
          rwa [rightLocalAction_val])
    rw [rightFlagSylow_quotient] at hq
    rw [f_val]
    simpa only [map_mul,map_inv,rightQuotientProjection_action] using hq
  obtain ⟨g,hg,he⟩ := rightLinearAction_semilinear_borel M a
  rw [fieldAut_eq] at he
  apply FiniteField.BinaryTorusTwoPower.eq_one_of_fixed_residual
    (n := 4) (k := k) M.local_field_card (by decide) (by decide) _
    (by rw [←map_pow,ha,map_one])
  intro u hu
  let t := Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear.torusProjection M.F
  have ht : Function.Surjective t :=
    Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear.torusProjection_surjective M.F
  rw [←map_pResidual_of_surjective 3 t ht] at hu
  obtain ⟨x,hx,rfl⟩ := hu
  apply (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear.borelActor_commutator_mem_core_iff
    M.F (n := 4) M.local_field_card ⟨g,hg⟩ (rightCoefficient M a) x).mp
  rw [Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear.twoCoreIn_eq_kernel M.F (n := 4) M.local_field_card,←he]
  exact hdisp x hx


private def scalarFlagHom : M.Fˣ →* flagAutomorphisms M where
  toFun := scalarFlag M
  map_one' := by
    apply Subtype.ext
    change Theory.SpecificGroups.UnitaryFive.Descent.unitaryConj M.form
      (Theory.SpecificGroups.UnitaryFive.FlagAutomorphisms.scalarUnitary M.form
        M.rightLeviTrace M.rightLeviTrace_spec M.matrix 1) = 1
    rw [map_one]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp [Theory.SpecificGroups.UnitaryFive.Descent.unitaryConj_apply_val]
  map_mul' k l := by
    apply Subtype.ext
    change Theory.SpecificGroups.UnitaryFive.Descent.unitaryConj M.form
      (Theory.SpecificGroups.UnitaryFive.FlagAutomorphisms.scalarUnitary M.form
        M.rightLeviTrace M.rightLeviTrace_spec M.matrix (k*l)) = _
    rw [map_mul,Theory.SpecificGroups.UnitaryFive.Descent.unitaryConj_mul]
    rfl

/-- Trivial plane field coefficient leaves only an inner flag correction
and the actual odd scalar actor; no involution assumption is used. -/
theorem coefficient_kernel_representation (a : flagAutomorphisms M)
    (ha : rightCoefficient M a = 1) :
    ∃ (b : M.overlap) (k : M.Fˣ), a = innerFlag M b * scalarFlag M k := by
  obtain ⟨b₀,β,_,he,hq⟩ := rightLinearAction_normalize M a
  rw [ha] at hq
  have hfield : Theory.PSL2.fieldAut (1 : M.F ≃+* M.F) = 1 := by
    rw [fieldAut_eq]
    change Atlas.RankOneFieldAutomorphisms.pslFieldAction 1 = 1
    exact map_one _
  rw [hfield] at hq
  obtain ⟨t,ht⟩ := Theory.SpecificGroups.UnitaryFive.PlaneCore.ResidualAction.exists_order_fifteen M.local_field_card
  obtain ⟨v,b₁,γ,_,hγ,hγq,hfix⟩ := native_torus_normalize M β hq t ht
  obtain ⟨k,hk,hx,hz⟩ := Theory.SpecificGroups.UnitaryFive.FlagAutomorphisms.radicalAction_full_scalar
    M.form M.conjugation M.rightLeviTrace M.rightLeviTrace_spec (rightCoordinateAction M γ)
    (rightCoordinateAction_right M γ hγq) t ht hfix
  have hs := normalized_eq_scalarFlag M γ hγq k hk t ht hfix hx hz
  exact ⟨b₀*b₁,Units.mk0 k hk,by rw [he,hγ,hs,map_mul,mul_assoc]⟩

/-- Every two-element in the plane coefficient kernel is inner on the
whole PSU₅(4) carrier. The scalar group has odd order fifteen. -/
theorem inner_of_twoPower_coefficient_eq_one (a : flagAutomorphisms M)
    (k : ℕ) (ha : a^(2^k)=1) (hc : rightCoefficient M a = 1) :
    a.val ∈ MulAut.innerSubgroup M.Carrier := by
  obtain ⟨b,c,he⟩ := coefficient_kernel_representation M a hc
  let q : flagAutomorphisms M →* (MulAut M.Carrier ⧸ MulAut.innerSubgroup M.Carrier) :=
    (QuotientGroup.mk' _).comp (flagAutomorphisms M).subtype
  have hb : q (innerFlag M b) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨b.val,rfl⟩
  have hq : q a = q (scalarFlag M c) := by rw [he,map_mul,hb,one_mul]
  have hc15 : c^15=1 := by
    have hh := pow_card_eq_one' (x := c)
    simpa only [Nat.card_units,M.local_field_card] using hh
  have h15 : (q a)^15=1 := by
    rw [hq,←map_pow]
    change q ((scalarFlagHom M c)^15) = 1
    rw [←map_pow,hc15,map_one,map_one]
  have htwo : (q a)^(2^k)=1 := by rw [←map_pow,ha,map_one]
  apply (QuotientGroup.eq_one_iff _).mp
  change q a = 1
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 2 15).pow_left k)
    (orderOf_dvd_of_pow_eq_one htwo) (orderOf_dvd_of_pow_eq_one h15)

end OriginalUnitaryFive
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
