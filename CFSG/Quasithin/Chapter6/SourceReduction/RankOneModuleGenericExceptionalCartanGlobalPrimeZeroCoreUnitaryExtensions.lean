module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreUnitaryModels
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension.Intermediate
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.Exclusion

/-!
# Unitary extension restrictions on the original Cartan pair

An original pair marked in an intermediate subgroup of the concrete
degree-two unitary extension restricts to the ordinary or full extended
flag amalgam. The preceding model exclusions then rule out either
orientation, at every positive field degree. This transports the original
full overlap, not just a minimal Sylow subgroup, and uses the same selected R.

The regular comparison retains both commuting squares. Its full-extension
branch is removed by the existing overlap-normality obstruction; the
remaining base branch has its explicit ordinary marking. This is a
restriction of an actual extension marking, not exhaustive recognition.
Reduction of arbitrary DGS outer extensions to this native extension and
the other original DGS rows remain source obligations.

For U₅(q), the original quasithin bound forces q = 4 from the actual
base-line-parabolic embedding in either orientation. The surviving base
endpoint then cannot embed in the source's solvable left parabolic. This
excludes arbitrary U₅ extensions without collapsing them to the pure model.
Both base embeddings are explicit; no quotient action or model isomorphism
is invented.

Source: Aschbacher–Smith F.1.12, pp.263–264, applied in 5.2.2, pp.647–648.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterF.GreenBook ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]

/-- The literal regular marking collapses to the ordinary endpoint maps.
The source Sylow remains the original sourceS throughout. -/
theorem LocalData.zeroCore_unitaryIntermediate_restriction
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (m : ℕ) (hm : 1 ≤ m) (Y : Subgroup (Extension.ProjectiveExtension m hm))
    (hY : Extension.Intermediate.base m hm ≤ Y)
    (e : RankTwoAmalgam.Iso (zeroCoreAmalgam L H B D R)
      (Extension.Intermediate.amalgam m hm Y)) :
    Y = Extension.Intermediate.base m hm ∧
      Nonempty (RankTwoAmalgam.Iso (zeroCoreAmalgam L H B D R) (amalgam m hm)) := by
  rcases Extension.Intermediate.intermediate_eq_base_or_top m hm Y hY with rfl | rfl
  · exact ⟨rfl,⟨e.trans (Extension.Intermediate.baseIso m hm)⟩⟩
  · exact ((d.zeroCore_not_unitaryFourExtension_parabolic h hH c hd hz m hm).1
      ⟨(e.trans (Extension.Intermediate.topIso m hm)).toParabolicEquiv⟩).elim

/-- Every intermediate native unitary extension is excluded on the same
source pair, with either endpoint orientation and the whole overlap. -/
theorem LocalData.zeroCore_not_unitaryIntermediate_parabolic
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (m : ℕ) (hm : 1 ≤ m) (Y : Subgroup (Extension.ProjectiveExtension m hm))
    (hY : Extension.Intermediate.base m hm ≤ Y) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      (Extension.Intermediate.amalgam m hm Y)) ∧
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      (Extension.Intermediate.amalgam m hm Y).reverse) := by
  rcases Extension.Intermediate.marked_alternatives m hm Y hY with ha | ha
  · obtain ⟨a⟩ := ha
    have he := d.zeroCore_not_unitaryFour_parabolic h hH c hd hz m hm
    exact ⟨fun ⟨e⟩ => he.1 ⟨e.trans a.toParabolicEquiv⟩,
      fun ⟨e⟩ => he.2 ⟨e.trans a.reverse.toParabolicEquiv⟩⟩
  · obtain ⟨a⟩ := ha
    have he := d.zeroCore_not_unitaryFourExtension_parabolic h hH c hd hz m hm
    exact ⟨fun ⟨e⟩ => he.1 ⟨e.trans a.toParabolicEquiv⟩,
      fun ⟨e⟩ => he.2 ⟨e.trans a.reverse.toParabolicEquiv⟩⟩

private theorem no_left_embedding {X : Type*} [Group X] [Group.IsSolvable X]
    (M : UnitaryFive.Model 4) (f : M.leftParabolic →* X) (hf : Function.Injective f) :
    False := by
  let : Group.IsSolvable M.leftParabolic := Group.isSolvable_of_isSolvable_injective hf
  have hq := Group.isSolvable_of_surjective
    (f := M.leftLocalQuotientEquiv.toMonoidHom) M.leftLocalQuotientEquiv.surjective
  exact Group.IsPerfect.not_isSolvable M.LocalUnitaryGroup hq

private theorem no_right_embedding {X : Type*} [Group X] [Group.IsSolvable X]
    (M : UnitaryFive.Model 4) (f : M.rightParabolic →* X) (hf : Function.Injective f) :
    False := by
  let : Group.IsSolvable M.rightParabolic := Group.isSolvable_of_isSolvable_injective hf
  let : Group.IsSolvable M.LocalLinearGroup := Group.isSolvable_of_surjective
    (f := M.rightLocalQuotientEquiv.toMonoidHom) M.rightLocalQuotientEquiv.surjective
  have hF : 2 < Nat.card M.F := by rw [M.local_field_card]; decide
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_perfect hF
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple hF
  have hs := Group.isSolvable_of_isSolvable_injective
    (f := (Theory.PSL2.sl2QuotientEquiv M.F).toMonoidHom)
    (Theory.PSL2.sl2QuotientEquiv M.F).injective
  exact Group.IsPerfect.not_isSolvable SL(2,M.F) hs

/-- An arbitrary extension of a U₅(q) pair cannot mark the original
mixed pair: the native base embeddings force q = 4 and then contradict
left solvability. No conclusion identifying the extension with its base
is needed, and both endpoint orientations are retained. -/
theorem LocalData.zeroCore_not_unitaryFive_extension
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    {q : ℕ} (hq : IsPrimePow q) (heven : Even q) (M : UnitaryFive.Model q)
    {X C Y : Type*} [Group X] [Group C] [Group Y] (β : RankTwoAmalgam X C Y)
    (iX : M.leftParabolic →* X) (hiX : Function.Injective iX)
    (iY : M.rightParabolic →* Y) (hiY : Function.Injective iY) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R) β) ∧
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R) β.reverse) := by
  let P := (D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)
  let Q := R ⊔ Global.sourceS L H
  let := (d.zeroCore_mixed_solvability h hH c hd hz).1
  constructor
  · rintro ⟨e⟩
    let f : M.leftParabolic →* P := e.left.symm.toMonoidHom.comp iX
    have hf : Function.Injective f := e.left.symm.injective.comp hiX
    have hq4 := M.field_size_eq_four_of_parabolic_embedding hq heven h.qtke.quasithin
      (P.subtype.comp f) (P.subtype_injective.comp hf)
    subst q
    exact no_left_embedding M f hf
  · rintro ⟨e⟩
    let f : M.leftParabolic →* Q := e.right.symm.toMonoidHom.comp iX
    have hf : Function.Injective f := e.right.symm.injective.comp hiX
    have hq4 := M.field_size_eq_four_of_parabolic_embedding hq heven h.qtke.quasithin
      (Q.subtype.comp f) (Q.subtype_injective.comp hf)
    subst q
    exact no_right_embedding M (e.left.symm.toMonoidHom.comp iY)
      (e.left.symm.injective.comp hiY)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
