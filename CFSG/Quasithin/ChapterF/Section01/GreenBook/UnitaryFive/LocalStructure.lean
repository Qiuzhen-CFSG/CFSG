module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Setup
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Source

/-!
# Local structure of the unitary-five parabolics

For every even prime power, including two, projective line shears construct a
nontrivial normal two-subgroup in the line parabolic. At parameter four the
matrix Levi decompositions identify the source local groups with the two
parabolic residuals. Their canonical cores have the source orders, and their
actual quotient groups are SU₃(4) and PSL₂(16).

The theorem `source_local_structure` assembles the local row of F.1.12(7) and
the perfectness and containment assertions of F.1.12(II)(i), for the residuals
embedded in the common projective carrier. `source_amalgam_marking` identifies
the source Borel and parabolics with the original full-overlap amalgam and
supplies its centralization label. All mathematical inputs are the field and
form data of `Model`; the matrix and group-theoretic calculations discharge
the local structural assertions.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.11--12, printed pp. 262--264.
-/

public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model

open scoped Pointwise

/-- Every even prime-power parameter has an actual model with a nontrivial
normal two-subgroup of its line parabolic, including parameter two. -/
theorem exists_model_with_left_normal_two_subgroup {q : ℕ}
    (hq : IsPrimePow q) (heven : Even q) :
    ∃ M : Model q, ∃ Q : Subgroup M.leftParabolic,
      Q.Normal ∧ Q ≠ ⊥ ∧ IsPGroup 2 Q := by
  obtain ⟨M⟩ := model_nonempty hq heven
  exact ⟨M, M.exists_left_normal_two_subgroup⟩

variable (M : Model 4)

/-- F.1.12(7) and (II)(i) for the constructed U₅(4) model. The groups in
these quotient, core and residual assertions are the same subgroups of the
common carrier used by the source amalgam. The special-core assertion spells
out the full meaning of the notation in F.1.11. -/
theorem source_local_structure :
    Source.IsSU (M.leftLocalImage ⧸ pCore 2 M.leftLocalImage) 3 4 ∧
    IsPGroup 2 (pCore 2 M.leftLocalImage) ∧
    Nat.card (pCore 2 M.leftLocalImage) = 4 ^ 7 ∧
    Nat.card (Subgroup.center (pCore 2 M.leftLocalImage)) = 4 ∧
    Subgroup.center (pCore 2 M.leftLocalImage) = commutator (pCore 2 M.leftLocalImage) ∧
    Subgroup.center (pCore 2 M.leftLocalImage) = frattini (pCore 2 M.leftLocalImage) ∧
    ClassicalGroup.IsPSL (M.rightLocalImage ⧸ pCore 2 M.rightLocalImage) 2 16 ∧
    Nat.card (pCore 2 M.rightLocalImage) = 2 ^ 16 ∧
    (Subgroup.solvableResidual M.leftLocalImage).map M.leftLocalImage.subtype =
      M.leftLocalImage ∧
    (Subgroup.solvableResidual M.rightLocalImage).map M.rightLocalImage.subtype =
      M.rightLocalImage ∧
    M.flagTwoSubgroup ≤ M.leftLocalImage ⊓ M.rightLocalImage := by
  obtain ⟨hp, hc, hz, hcomm, hfrat⟩ := M.leftLocalImage_core_structure
  exact ⟨M.source_quotient_models.1, hp, hc, hz, hcomm, hfrat,
    M.source_quotient_models.2, M.rightLocalImage_core_card,
    M.leftLocalImage_residual, M.rightLocalImage_residual,
    le_inf M.flagTwoSubgroup_le_leftLocalImage M.flagTwoSubgroup_le_rightLocalImage⟩

/-- The source definitions recover the actual marked parabolic amalgam. The
normality is relative to the whole overlap, and the displayed product uses
the literal source Sylow normalizers. The line side has the source label L₁
because it centralizes the actual embedded Z(S). -/
theorem source_amalgam_marking :
    Source.commonBorel M.sourceLocals M.flagTwoSubgroup = M.overlap ∧
    Source.parabolic M.sourceLocals M.flagTwoSubgroup 0 = M.leftParabolic ∧
    Source.parabolic M.sourceLocals M.flagTwoSubgroup 1 = M.rightParabolic ∧
    (M.flagTwoSubgroup.subgroupOf M.overlap).Normal ∧
    Nat.card M.flagTwoSubgroup = 2 ^ 20 ∧
    M.flagTwoSubgroup.relIndex M.overlap = 45 ∧
    (M.overlap : Set M.Carrier) =
      (Source.borel M.leftLocalImage M.flagTwoSubgroup : Set M.Carrier) *
        (Source.borel M.rightLocalImage M.flagTwoSubgroup : Set M.Carrier) *
          (M.flagTwoSubgroup : Set M.Carrier) ∧
    M.leftLocalImage ≤ Subgroup.centralizer (M.flagCenter : Set M.Carrier) := by
  refine ⟨M.source_commonBorel, M.source_parabolic_left, M.source_parabolic_right,
    M.flagTwoSubgroup_normal_in_overlap, M.flagTwoSubgroup_card,
    M.flagTwoSubgroup_relIndex_overlap, ?_, M.leftLocalImage_le_centralizer_flagCenter⟩
  rw [M.source_borel_left, M.source_borel_right]
  exact M.overlap_eq_borel_product

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
