module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Marking
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs
public import Theory.GroupTheory.Amalgam.LocalStructure

/-!
# The source local groups inside the U₅(4) carrier

The matrix calculations identify the intrinsic residuals of the line and plane
parabolics. Here their subtype inclusions identify those residuals with actual
subgroups L₁ and L₂ of the common projective carrier. Canonical two-cores,
quotients, special-core structure and Sylow markings are transported through
these inclusions, with equations on quotient representatives.

The intrinsic Sylow normalizers are exactly the literal `Source.borel`
subgroups. Consequently `Source.commonBorel` is the original full flag overlap,
and `Source.parabolic` gives the original line and plane stabilizers. This
supplies the quotient, Sylow and normalization clauses of F.1.1 and the residual
and containment clauses of F.1.12(II)(i) for the concrete model.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.1, F.1.3 and F.1.11--12(7), printed pp.259--264.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model

open Theory.GroupTheory
open scoped Pointwise

variable (M : Model 4)

/-- The actual inclusion of the left residual into the common carrier. -/
noncomputable def leftLocalImageEquiv : M.leftLocal ≃* M.leftLocalImage :=
  M.leftLocal.equivMapOfInjective M.leftParabolic.subtype Subtype.val_injective

/-- The actual inclusion of the right residual into the common carrier. -/
noncomputable def rightLocalImageEquiv : M.rightLocal ≃* M.rightLocalImage :=
  M.rightLocal.equivMapOfInjective M.rightParabolic.subtype Subtype.val_injective

@[simp] theorem leftLocalImageEquiv_val (g : M.leftLocal) :
    (M.leftLocalImageEquiv g : M.Carrier) = g.val.val := rfl

@[simp] theorem rightLocalImageEquiv_val (g : M.rightLocal) :
    (M.rightLocalImageEquiv g : M.Carrier) = g.val.val := rfl

instance leftLocalImage_isPerfect : Group.IsPerfect M.leftLocalImage :=
  Group.IsPerfect.ofSurjective (f := M.leftLocalImageEquiv.toMonoidHom)
    M.leftLocalImageEquiv.surjective

instance rightLocalImage_isPerfect : Group.IsPerfect M.rightLocalImage :=
  Group.IsPerfect.ofSurjective (f := M.rightLocalImageEquiv.toMonoidHom)
    M.rightLocalImageEquiv.surjective

/-- F.1.12(II)(i): L₁ equals its terminal derived subgroup in the carrier. -/
theorem leftLocalImage_residual :
    (Subgroup.solvableResidual M.leftLocalImage).map M.leftLocalImage.subtype =
      M.leftLocalImage := by
  rw [Subgroup.solvableResidual_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- F.1.12(II)(i): L₂ equals its terminal derived subgroup in the carrier. -/
theorem rightLocalImage_residual :
    (Subgroup.solvableResidual M.rightLocalImage).map M.rightLocalImage.subtype =
      M.rightLocalImage := by
  rw [Subgroup.solvableResidual_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- The quotient of the embedded L₁ by its canonical core is the actual SU₃(4). -/
noncomputable def leftLocalImageQuotientEquiv :
    (M.leftLocalImage ⧸ pCore 2 M.leftLocalImage) ≃* M.LocalUnitaryGroup :=
  (LocalCoreTransport.quotientEquiv 2 M.leftLocalImageEquiv.symm).trans
    M.leftLocalQuotientEquiv

/-- The quotient of the embedded L₂ by its canonical core is the actual PSL₂(16). -/
noncomputable def rightLocalImageQuotientEquiv :
    (M.rightLocalImage ⧸ pCore 2 M.rightLocalImage) ≃* M.LocalLinearGroup :=
  (LocalCoreTransport.quotientEquiv 2 M.rightLocalImageEquiv.symm).trans
    M.rightLocalQuotientEquiv

/-- The embedded quotient uses the original matrix Levi projection. -/
@[simp] theorem leftLocalImageQuotientEquiv_mk (g : M.leftLocal) :
    M.leftLocalImageQuotientEquiv (QuotientGroup.mk (M.leftLocalImageEquiv g)) =
      M.leftLocalLevi g := by
  simp [leftLocalImageQuotientEquiv]

/-- The embedded quotient uses the original SL₂ projection and projective quotient. -/
@[simp] theorem rightLocalImageQuotientEquiv_mk (g : M.rightLocal) :
    M.rightLocalImageQuotientEquiv (QuotientGroup.mk (M.rightLocalImageEquiv g)) =
      QuotientGroup.mk (M.rightLocalProjection g) := by
  simp [rightLocalImageQuotientEquiv]

/-- The source two-core is the full line-unipotent subgroup in the same carrier. -/
theorem leftLocalImage_twoCore : Source.twoCore M.leftLocalImage =
    M.lineUnipotent.map M.leftParabolic.subtype := by
  rw [Source.twoCore, ← pCore_map_iso 2 M.leftLocalImageEquiv, Subgroup.map_map]
  change (pCore 2 M.leftLocal).map
    (M.leftParabolic.subtype.comp M.leftLocal.subtype) = _
  rw [← Subgroup.map_map, M.map_leftCore_subtype]

/-- The source two-core is the full plane-unipotent subgroup in the same carrier. -/
theorem rightLocalImage_twoCore : Source.twoCore M.rightLocalImage =
    M.rightUnipotent.map M.rightParabolic.subtype := by
  rw [Source.twoCore, ← pCore_map_iso 2 M.rightLocalImageEquiv, Subgroup.map_map]
  change (pCore 2 M.rightLocal).map
    (M.rightParabolic.subtype.comp M.rightLocal.subtype) = _
  rw [← Subgroup.map_map, M.rightLocal_pCore_map]

/-- The complete special-group meaning of 4^(1+6) from F.1.11, for canonical O₂(L₁). -/
theorem leftLocalImage_core_structure :
    IsPGroup 2 (pCore 2 M.leftLocalImage) ∧
    Nat.card (pCore 2 M.leftLocalImage) = 4 ^ 7 ∧
    Nat.card (Subgroup.center (pCore 2 M.leftLocalImage)) = 4 ∧
    Subgroup.center (pCore 2 M.leftLocalImage) = commutator (pCore 2 M.leftLocalImage) ∧
    Subgroup.center (pCore 2 M.leftLocalImage) = frattini (pCore 2 M.leftLocalImage) := by
  let e := LocalCoreTransport.coreEquiv 2 M.leftLocalImageEquiv.symm
  refine ⟨pCore_isPGroup, (Nat.card_congr e.toEquiv).trans M.card_leftCore,
    (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans M.card_center_leftCore, ?_, ?_⟩
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.center_map_equiv e, map_commutator_eq,
      MonoidHom.range_eq_top.mpr e.surjective, ← commutator_def]
    exact M.commutator_leftCore.symm
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.center_map_equiv e, Subgroup.frattini_map_equiv e]
    exact M.frattini_leftCore.symm

/-- The source order of canonical O₂(L₂). -/
theorem rightLocalImage_core_card : Nat.card (pCore 2 M.rightLocalImage) = 2 ^ 16 :=
  (LocalCoreTransport.core_card 2 M.rightLocalImageEquiv.symm).trans M.rightLocal_pCore_card

/-- The common Sylow as a Sylow subgroup of the embedded L₁. -/
noncomputable def leftLocalImageSylow : Sylow 2 M.leftLocalImage :=
  M.leftLocalSylow.mapSurjective (f := M.leftLocalImageEquiv.toMonoidHom)
    M.leftLocalImageEquiv.surjective

/-- The common Sylow as a Sylow subgroup of the embedded L₂. -/
noncomputable def rightLocalImageSylow : Sylow 2 M.rightLocalImage :=
  M.rightLocalSylow.mapSurjective (f := M.rightLocalImageEquiv.toMonoidHom)
    M.rightLocalImageEquiv.surjective

/-- The embedded left Sylow is the original matrix flag subgroup. -/
theorem leftLocalImageSylow_map :
    (M.leftLocalImageSylow : Subgroup M.leftLocalImage).map M.leftLocalImage.subtype =
      M.flagTwoSubgroup := by
  change ((M.leftLocalSylow : Subgroup M.leftLocal).map
    M.leftLocalImageEquiv.toMonoidHom).map M.leftLocalImage.subtype = _
  rw [Subgroup.map_map]
  exact M.leftLocalSylow_carrier_map

/-- The embedded right Sylow is the original matrix flag subgroup. -/
theorem rightLocalImageSylow_map :
    (M.rightLocalImageSylow : Subgroup M.rightLocalImage).map M.rightLocalImage.subtype =
      M.flagTwoSubgroup := by
  change ((M.rightLocalSylow : Subgroup M.rightLocal).map
    M.rightLocalImageEquiv.toMonoidHom).map M.rightLocalImage.subtype = _
  rw [Subgroup.map_map]
  exact M.rightLocalSylow_carrier_map

/-- The source N_L₁(S ∩ L₁) is the constructed left intrinsic normalizer image. -/
theorem source_borel_left :
    Source.borel M.leftLocalImage M.flagTwoSubgroup = M.leftSylowNormalizerImage := by
  unfold Source.borel
  rw [inf_of_le_left M.flagTwoSubgroup_le_leftLocalImage]
  have h := congrArg (Subgroup.map M.leftLocalImage.subtype)
    (Subgroup.subgroupOf_normalizer_eq M.flagTwoSubgroup_le_leftLocalImage)
  rw [Subgroup.subgroupOf_map_subtype] at h
  rw [inf_comm, h]
  have hS : M.flagTwoSubgroup.subgroupOf M.leftLocalImage =
      (M.leftLocalImageSylow : Subgroup M.leftLocalImage) := by
    apply Subgroup.map_injective (f := M.leftLocalImage.subtype) Subtype.val_injective
    rw [Subgroup.map_subgroupOf_eq_of_le M.flagTwoSubgroup_le_leftLocalImage,
      M.leftLocalImageSylow_map]
  rw [hS]
  change (Subgroup.normalizer ((M.leftLocalSylow : Subgroup M.leftLocal).map
    M.leftLocalImageEquiv.toMonoidHom : Set M.leftLocalImage)).map
      M.leftLocalImage.subtype = _
  rw [← Subgroup.map_equiv_normalizer_eq, Subgroup.map_map]
  rfl

/-- The source N_L₂(S ∩ L₂) is the constructed right intrinsic normalizer image. -/
theorem source_borel_right :
    Source.borel M.rightLocalImage M.flagTwoSubgroup = M.rightSylowNormalizerImage := by
  unfold Source.borel
  rw [inf_of_le_left M.flagTwoSubgroup_le_rightLocalImage]
  have h := congrArg (Subgroup.map M.rightLocalImage.subtype)
    (Subgroup.subgroupOf_normalizer_eq M.flagTwoSubgroup_le_rightLocalImage)
  rw [Subgroup.subgroupOf_map_subtype] at h
  rw [inf_comm, h]
  have hS : M.flagTwoSubgroup.subgroupOf M.rightLocalImage =
      (M.rightLocalImageSylow : Subgroup M.rightLocalImage) := by
    apply Subgroup.map_injective (f := M.rightLocalImage.subtype) Subtype.val_injective
    rw [Subgroup.map_subgroupOf_eq_of_le M.flagTwoSubgroup_le_rightLocalImage,
      M.rightLocalImageSylow_map]
  rw [hS]
  change (Subgroup.normalizer ((M.rightLocalSylow : Subgroup M.rightLocal).map
    M.rightLocalImageEquiv.toMonoidHom : Set M.rightLocalImage)).map
      M.rightLocalImage.subtype = _
  rw [← Subgroup.map_equiv_normalizer_eq, Subgroup.map_map]
  rfl

/-- The source pair, in the order fixed by the centralization convention. -/
def sourceLocals (i : Fin 2) : Subgroup M.Carrier :=
  if i = 0 then M.leftLocalImage else M.rightLocalImage

@[simp] theorem sourceLocals_zero : M.sourceLocals 0 = M.leftLocalImage := if_pos rfl

@[simp] theorem sourceLocals_one : M.sourceLocals 1 = M.rightLocalImage := if_neg (by decide)

/-- The literal source B₁ B₂ S recovers the original full overlap. -/
theorem source_commonBorel : Source.commonBorel M.sourceLocals M.flagTwoSubgroup =
    M.overlap := by
  simp only [Source.commonBorel, M.sourceLocals_zero, M.sourceLocals_one,
    M.source_borel_left, M.source_borel_right]
  exact M.sylowNormalizerImages_sup_flagTwoSubgroup

/-- The source quotient predicates are witnessed by the actual matrix equivalences. -/
theorem source_quotient_models :
    Source.IsSU (M.leftLocalImage ⧸ pCore 2 M.leftLocalImage) 3 4 ∧
    ClassicalGroup.IsPSL (M.rightLocalImage ⧸ pCore 2 M.rightLocalImage) 2 16 :=
  ⟨⟨M.F, inferInstance, inferInstance, M.localUnitaryForm, M.card,
      M.localUnitaryForm_conjugation, ⟨M.leftLocalImageQuotientEquiv⟩⟩,
    ⟨M.F, inferInstance, inferInstance, M.local_field_card,
      ⟨M.rightLocalImageQuotientEquiv⟩⟩⟩

/-- F.1.1(c), with exponents two for SU₃(4) and four for PSL₂(16). -/
theorem source_rankOne_models (i : Fin 2) :
    Source.IsRankOneModel (M.sourceLocals i ⧸ pCore 2 (M.sourceLocals i)) := by
  fin_cases i
  · exact .special_unitary 2 (by decide) M.source_quotient_models.1
  · exact .linear 4 (by decide) M.source_quotient_models.2

/-- The source L₁ S B₂ is the full line parabolic. -/
theorem source_parabolic_left :
    Source.parabolic M.sourceLocals M.flagTwoSubgroup 0 = M.leftParabolic := by
  change M.leftLocalImage ⊔ M.flagTwoSubgroup ⊔
    Source.borel M.rightLocalImage M.flagTwoSubgroup = _
  rw [M.source_borel_right, sup_of_le_left M.flagTwoSubgroup_le_leftLocalImage]
  have hB : M.leftSylowNormalizerImage ≤ M.leftLocalImage := by
    rw [M.leftSylowNormalizerImage_eq]
    exact inf_le_left
  calc
    _ = M.leftLocalImage ⊔
        (M.leftSylowNormalizerImage ⊔ M.rightSylowNormalizerImage) := by
      rw [← sup_assoc, sup_of_le_left hB]
    _ = _ := by rw [M.sylowNormalizerImages_sup, M.leftLocalImage_sup_overlap]

/-- The source L₂ S B₁ is the full plane parabolic. -/
theorem source_parabolic_right :
    Source.parabolic M.sourceLocals M.flagTwoSubgroup 1 = M.rightParabolic := by
  change M.rightLocalImage ⊔ M.flagTwoSubgroup ⊔
    Source.borel M.leftLocalImage M.flagTwoSubgroup = _
  rw [M.source_borel_left, sup_of_le_left M.flagTwoSubgroup_le_rightLocalImage]
  have hB : M.rightSylowNormalizerImage ≤ M.rightLocalImage := by
    rw [M.rightSylowNormalizerImage_eq]
    exact inf_le_left
  calc
    _ = M.rightLocalImage ⊔
        (M.rightSylowNormalizerImage ⊔ M.leftSylowNormalizerImage) := by
      rw [← sup_assoc, sup_of_le_left hB]
    _ = _ := by rw [sup_comm M.rightSylowNormalizerImage,
      M.sylowNormalizerImages_sup, M.rightLocalImage_sup_overlap]

/-- F.1.1(b), with the literal intersection S ∩ Lᵢ and subtype map. -/
theorem source_sylow (i : Fin 2) :
    ∃ T : Sylow 2 (M.sourceLocals i),
      (T : Subgroup (M.sourceLocals i)).map (M.sourceLocals i).subtype =
        M.flagTwoSubgroup ⊓ M.sourceLocals i := by
  fin_cases i
  · exact ⟨M.leftLocalImageSylow, M.leftLocalImageSylow_map.trans
      (inf_of_le_left M.flagTwoSubgroup_le_leftLocalImage).symm⟩
  · exact ⟨M.rightLocalImageSylow, M.rightLocalImageSylow_map.trans
      (inf_of_le_left M.flagTwoSubgroup_le_rightLocalImage).symm⟩

/-- Relative normality of the residuals makes the full overlap normalize each Lᵢ. -/
theorem overlap_normalizes_sourceLocals (i : Fin 2) :
    M.overlap ≤ Subgroup.normalizer (M.sourceLocals i : Set M.Carrier) := by
  fin_cases i
  · exact (show M.overlap ≤ M.leftParabolic from inf_le_left).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (show M.leftLocalImage ≤ M.leftParabolic from
          (Subgroup.map_le_range _ _).trans_eq (Subgroup.range_subtype _))).mp
            M.leftLocalImage_normal_in_parabolic)
  · exact (show M.overlap ≤ M.rightParabolic from inf_le_right).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (show M.rightLocalImage ≤ M.rightParabolic from
          (Subgroup.map_le_range _ _).trans_eq (Subgroup.range_subtype _))).mp
            M.rightLocalImage_normal_in_parabolic)

/-- F.1.1(a): the actual common two-subgroup normalizes both source local groups. -/
theorem source_sylow_normalizes (i : Fin 2) :
    M.flagTwoSubgroup ≤ Subgroup.normalizer (M.sourceLocals i : Set M.Carrier) :=
  M.flagTwoSubgroup_le_overlap.trans (M.overlap_normalizes_sourceLocals i)

/-- F.1.1(d): the literal source Bⱼ normalizes Lᵢ. -/
theorem source_cross_normalizes (i : Fin 2) :
    Source.borel (M.sourceLocals (Source.other i)) M.flagTwoSubgroup ≤
      Subgroup.normalizer (M.sourceLocals i : Set M.Carrier) := by
  apply le_trans _ (M.overlap_normalizes_sourceLocals i)
  fin_cases i
  · change Source.borel M.rightLocalImage M.flagTwoSubgroup ≤ _
    rw [M.source_borel_right, M.rightSylowNormalizerImage_eq]
    exact inf_le_right
  · change Source.borel M.leftLocalImage M.flagTwoSubgroup ≤ _
    rw [M.source_borel_left, M.leftSylowNormalizerImage_eq]
    exact inf_le_right

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
