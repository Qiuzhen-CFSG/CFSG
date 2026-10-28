module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.Exclusion

/-!
# The U₅(4) source amalgam and its concrete marking

The literal source parabolics `Lᵢ S Bⱼ` and Borel `B₁ B₂ S` are the matrix
line and plane stabilizers and their full overlap. Their equality gives an
amalgam isomorphism whose two squares commute on each actual group element.
The local-structure exports use the same residual subgroups `Lᵢ`, canonical
two-cores and Sylow subgroup. Thus their SU₃(4), PSL₂(16) and special-core
calculations belong to this marked amalgam.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.11--12(7), printed pp.262--264.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model

open Theory.GroupTheory

variable (M : Model 4)

/-- The inclusion amalgam using the literal source groups. -/
noncomputable def sourceAmalgam :
    RankTwoAmalgam (Source.parabolic M.sourceLocals M.flagTwoSubgroup 0)
      (Source.commonBorel M.sourceLocals M.flagTwoSubgroup)
      (Source.parabolic M.sourceLocals M.flagTwoSubgroup 1) :=
  .ofSubgroups _ _ _
    (M.source_commonBorel.le.trans (inf_le_left.trans M.source_parabolic_left.ge))
    (M.source_commonBorel.le.trans (inf_le_right.trans M.source_parabolic_right.ge))

/-- Identity on the ambient elements identifies the source and matrix amalgams. -/
noncomputable def sourceAmalgamIso : RankTwoAmalgam.Iso M.sourceAmalgam M.amalgam :=
  RankTwoAmalgam.ofSubgroupsIso (MulEquiv.refl M.Carrier) _ _ inf_le_left inf_le_right
    ((Subgroup.map_id _).trans M.source_parabolic_left)
    ((Subgroup.map_id _).trans M.source_commonBorel)
    ((Subgroup.map_id _).trans M.source_parabolic_right)

/-- The literal source groups realize the U₅(4) alternative with compatible markings. -/
theorem sourceAmalgam_isAmalgam : IsAmalgam 4 M.sourceAmalgam :=
  ⟨M, ⟨M.sourceAmalgamIso⟩⟩

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
