module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.Geometry
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SourceCorrection
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.LocalStructure
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.Tits.FullRee

/-!
# The concrete Tits inclusion amalgam for the exceptional-model calculation

The model is attached to the actual Atlas group and the two specified Parrott
overgroups. The predicate below includes both commuting squares, so subsequent
local calculations can use `Theory.GroupTheory.Amalgam.LocalStructure`.
It makes no uniqueness assertion. The proved orders, exact Sylow overlap,
intrinsic cores and actual matrix quotients transport along the compatible
isomorphism. The marked derived-intersection comparison is exported as well.

The full binary Ree model and its identification with all automorphisms of Atlas
are exported from `Tits.FullRee`. The imported source correction proves that the printed first pair
in F.1.12(I)(9) cannot hold for any local subgroup inside the full first
parabolic. It also rules out a dihedral quotient of that full parabolic
independently of the proposed kernel. Thus the distinction between `L₁` and
`L₁S` does not repair the printed pair. The final group alternatives remain
the Tits group and its full automorphism extension.

Source: Aschbacher--Smith, F.1.12(I)(9), printed p. 263, and 14.2.21,
printed pp. 988--989; Parrott (1972), pp. 672, 683--684.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook

open Theory.GroupTheory

/-- Compatibility with the concrete Parrott inclusion amalgam, not merely
three unrelated group isomorphisms or a group-family label. -/
def IsAtlasTitsAmalgam {L B R : Type*} [Group L] [Group B] [Group R]
    (α : RankTwoAmalgam L B R) : Prop :=
  Nonempty (RankTwoAmalgam.Iso α Tits.ExceptionalParabolics.amalgam)

namespace IsAtlasTitsAmalgam

variable {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R}

/-- The orders belong to the full parabolics and the whole common overlap. -/
theorem cards (h : IsAtlasTitsAmalgam α) :
    Nat.card L = 10240 ∧ Nat.card B = 2048 ∧ Nat.card R = 6144 := by
  obtain ⟨e⟩ := h
  exact ⟨(Nat.card_congr e.left.toEquiv).trans Tits.ExceptionalParabolics.first_card,
    (Nat.card_congr e.middle.toEquiv).trans Tits.ExceptionalParabolics.overlap_card,
    (Nat.card_congr e.right.toEquiv).trans Tits.ExceptionalParabolics.second_card⟩

/-- The corrected first core and the unchanged second core, intrinsic to the
two full parabolics. The chosen source local factors equal these parabolics. -/
theorem core_cards (h : IsAtlasTitsAmalgam α) :
    Nat.card (pCore 2 L) = 512 ∧ Nat.card (pCore 2 R) = 1024 := by
  obtain ⟨e⟩ := h
  exact ⟨(LocalCoreTransport.core_card 2 e.left).trans
      Tits.ExceptionalParabolics.FirstQuotient.core_card,
    (LocalCoreTransport.core_card 2 e.right).trans
      Tits.ExceptionalParabolics.second_core_card⟩

/-- The quotient targets are the genuine Sz(2) and PSL₂(2) matrix carriers. -/
theorem core_quotients (h : IsAtlasTitsAmalgam α) :
    Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∧
    Nonempty ((R ⧸ pCore 2 R) ≃* ReeF4.LargeLocalSeeds.LinearQuotient 0) := by
  obtain ⟨e⟩ := h
  exact ⟨⟨(LocalCoreTransport.quotientEquiv 2 e.left).trans
      Tits.ExceptionalParabolics.FirstQuotient.coreQuotientEquiv⟩,
    ⟨(LocalCoreTransport.quotientEquiv 2 e.right).trans
      Tits.ExceptionalParabolics.secondCoreQuotientEquiv⟩⟩

/-- Both overlap maps agree with the actual Ree-derived intersection marking. -/
theorem derived_model (h : IsAtlasTitsAmalgam α) :
    Nonempty (RankTwoAmalgam.Iso α Tits.ExceptionalParabolics.FullRee.derivedAmalgam) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans Tits.ExceptionalParabolics.FullRee.atlasAmalgamIso⟩

/-- The same model identification uses the certified Sylow group as its middle group. -/
theorem sylow_model (h : IsAtlasTitsAmalgam α) :
    Nonempty (RankTwoAmalgam.Iso α Tits.ExceptionalParabolics.sylowAmalgam) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans Tits.ExceptionalParabolics.sylowAmalgamIso.symm⟩

/-- The source discrepancy persists under compatible model transport.
Here `L` is the full left parabolic, and the core is intrinsic to it. -/
theorem no_dihedral_left_core_quotient (h : IsAtlasTitsAmalgam α) :
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* DihedralGroup 5) := by
  obtain ⟨e⟩ := h
  rintro ⟨d⟩
  exact Tits.ExceptionalParabolics.first_no_dihedral_quotient _
    ⟨(LocalCoreTransport.quotientEquiv 2 e.left).symm.trans d⟩

end IsAtlasTitsAmalgam

/-- The actual derived-intersection model realizes the Atlas model predicate,
with no independent local-identification premise. -/
theorem isAtlasTitsAmalgam_derived :
    IsAtlasTitsAmalgam Tits.ExceptionalParabolics.FullRee.derivedAmalgam :=
  ⟨Tits.ExceptionalParabolics.FullRee.atlasAmalgamIso.symm⟩

end CFSG.Quasithin.ChapterF.GreenBook
