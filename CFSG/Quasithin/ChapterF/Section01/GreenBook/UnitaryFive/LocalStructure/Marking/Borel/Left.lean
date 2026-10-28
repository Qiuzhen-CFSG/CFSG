module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Marking.Borel.Right
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Borel.UnitaryLine

/-!
# The line-parabolic Borel normalizer

The transported SU₃ isotropic-line stabilizer is maximal, hence its preimage
is the maximal flag subgroup of the full line parabolic. It normalizes the
common Sylow by the plane-side calculation. The Sylow cannot be normal in
the parabolic: its order exceeds the proved canonical core order in the
residual. Maximality identifies the normalizer, and literal subtype maps
give the intrinsic residual normalizer and its common-carrier image.

Source: Aschbacher--Smith F.1.3 and F.1.12(7), printed pp.260 and 263--264.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open Matrix BenderSuzuki.MatrixGroups Theory.SpecificGroups.UnitaryFive
open LineCore
variable (M : Model 4)

/-- The marked isotropic-line stabilizer is maximal in the actual SU₃ Levi. -/
theorem localUnitaryLineStabilizer_isCoatom : IsCoatom M.localUnitaryLineStabilizer := by
  obtain ⟨c, hc⟩ := M.exists_lineTraceOne
  let J₀ := Source.Unitary.FormTransport.standardForm M.localUnitaryForm
  let C := Levi.lineBasis c
  have hC : M.localUnitaryForm.conjTranspose C.val * M.localUnitaryForm.form * C.val =
      J₀.form := Levi.lineBasis_gram M.localUnitaryForm rfl c hc
  let e := Source.Unitary.FormTransport.specialEquiv M.localUnitaryForm C hC
  have h := Levi.Borel.lineStabilizer_isCoatom_of_transport M.localUnitaryForm J₀
    M.local_field_card M.line_fixedField_card rfl C e
    (Source.Unitary.FormTransport.specialEquiv_apply M.localUnitaryForm C hC)
  have hf : C.val *ᵥ ![1, 0, 0] = ![1, 1, 0] := Levi.lineBasis_first c
  rw [hf, ← M.localUnitaryLine_eq_span] at h
  exact h

/-- The full flag subgroup is maximal in the line parabolic. -/
theorem overlap_leftParabolic_isCoatom : IsCoatom (M.overlap.subgroupOf M.leftParabolic) := by
  rw [← M.lineParabolicProjection_flag_preimage]
  exact Subgroup.isCoatom_comap_of_surjective M.lineParabolicProjection_surjective
    M.localUnitaryLineStabilizer_isCoatom

/-- The full line-parabolic Sylow normalizer is the flag overlap. -/
theorem leftParabolicSylow_normalizer :
    Subgroup.normalizer (M.leftParabolicSylow : Set M.leftParabolic) =
      M.overlap.subgroupOf M.leftParabolic := by
  have hBN : M.overlap.subgroupOf M.leftParabolic ≤
      Subgroup.normalizer (M.leftParabolicSylow : Set M.leftParabolic) := by
    have hn : M.overlap ≤ Subgroup.normalizer (M.flagTwoSubgroup : Set M.Carrier) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer M.flagTwoSubgroup_le_overlap).mp
        M.overlapSylow_normal
    intro g hg
    exact Subgroup.le_normalizer_comap M.leftParabolic.subtype (hn hg)
  have hne : Subgroup.normalizer (M.leftParabolicSylow : Set M.leftParabolic) ≠ ⊤ := by
    intro htop
    have : (M.leftParabolicSylow : Subgroup M.leftParabolic).Normal :=
      Subgroup.normalizer_eq_top_iff.mp htop
    have : (M.leftLocalSylow : Subgroup M.leftLocal).Normal :=
      Subgroup.normal_comap M.leftLocal.subtype
    have hle : (M.leftLocalSylow : Subgroup M.leftLocal) ≤ pCore 2 M.leftLocal :=
      le_sSup ⟨inferInstance, M.leftLocalSylow.isPGroup'⟩
    have hc := Subgroup.card_le_of_le hle
    have he := Subgroup.card_map_of_injective
      (K := (M.leftLocalSylow : Subgroup M.leftLocal))
      (f := M.leftParabolic.subtype.comp M.leftLocal.subtype)
      (Subtype.val_injective.comp Subtype.val_injective)
    rw [M.leftLocalSylow_carrier_map, M.flagTwoSubgroup_card] at he
    rw [← he, M.card_leftCore] at hc
    norm_num at hc
  rcases eq_or_lt_of_le hBN with h | h
  · exact h.symm
  · exact (hne (M.overlap_leftParabolic_isCoatom.2 _ h)).elim

/-- The intrinsic left residual normalizer is its intersection with the overlap. -/
theorem leftSylowNormalizer_eq_overlap :
    M.leftSylowNormalizer = (M.overlap.subgroupOf M.leftParabolic).subgroupOf M.leftLocal := by
  change Subgroup.normalizer ((M.leftParabolicSylow : Subgroup M.leftParabolic).subgroupOf
    M.leftLocal : Set M.leftLocal) = _
  rw [← Subgroup.subgroupOf_normalizer_eq (show (M.leftParabolicSylow : Subgroup M.leftParabolic) ≤ M.leftLocal from M.flagLeft_le_leftLocal)]
  change (Subgroup.normalizer (M.leftParabolicSylow : Set M.leftParabolic)).subgroupOf
    M.leftLocal = _
  rw [M.leftParabolicSylow_normalizer]

/-- The source B₁ is the literal intersection in the projective carrier. -/
theorem leftSylowNormalizerImage_eq :
    M.leftSylowNormalizerImage = M.leftLocalImage ⊓ M.overlap := by
  rw [leftSylowNormalizerImage, M.leftSylowNormalizer_eq_overlap, ← Subgroup.map_map,
    Subgroup.subgroupOf_map_subtype, Subgroup.map_inf _ _ _ Subtype.val_injective,
    Subgroup.map_subgroupOf_eq_of_le (show M.overlap ≤ M.leftParabolic from inf_le_left)]
  exact inf_comm _ _
end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
