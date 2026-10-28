module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreJanko
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionExceptional
public import BenderSuzuki.MatrixGroups.SuzukiZero

/-!
# The exceptional catalogue in the zero-core Cartan argument

The source prime pair has a nonsolvable right parabolic. Six fixed
exceptional rows have solvable parabolics on both sides, as follows from
their literal two-core quotients. The Hall–Janko rows are excluded using
the normal elementary subgroup in the original source Sylow. Consequently
neither orientation of any exceptional catalogue row occurs. Only raw
parabolic equivalence is needed, including in the Hall–Janko cases.

These exclusions concern the original pair and its whole overlap. They
do not assert the exhaustive F.1.12 recognition needed to obtain a model.
Source: Aschbacher–Smith 5.2.2, printed pp.647–648, and F.1.12(I)(8–13),
printed pp.262–264, refs/quasithin.pdf; the Tits two-core quotient is the
corrected Sz(2) quotient of the concrete model.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterF.GreenBook
variable {G : Type*} [Group G] [Finite G]

private theorem solvable_of_core_quotient {X Y : Type*} [Group X] [Finite X]
    [Group Y] [Group.IsSolvable Y] (e : X ⧸ pCore 2 X ≃* Y) : Group.IsSolvable X := by
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 X)).mpr
    ⟨inferInstance,Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective⟩

private theorem solvable_of_binary_quotient {X : Type*} [Group X] [Finite X]
    (h : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 2) : Group.IsSolvable X := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  let := Theory.PSL2.OuterSolvable.isSolvable_of_card_two hF
  exact solvable_of_core_quotient e

private theorem exceptional_left_solvable {X E Y : Type*} [Group X] [Group E] [Group Y]
    (k : ExceptionalModels.Case) (α : RankTwoAmalgam X E Y)
    (hj : k ≠ .j2) (ha : k ≠ .autJ2)
    (h : ExceptionalModels.ParabolicModel k α) : Group.IsSolvable X := by
  let : Group.IsSolvable (PSL(2,ZMod 2)) :=
    Theory.PSL2.OuterSolvable.isSolvable_of_card_two (by simp)
  let := BenderSuzuki.MatrixGroups.suzukiZero_isSolvable
  cases k with
  | j2 => exact (hj rfl).elim
  | autJ2 => exact (ha rfl).elim
  | g2Derived =>
    obtain ⟨e⟩ := h
    let := solvable_of_core_quotient Atlas.G2.ExceptionalLocalQuotients.derivedFirstQuotientEquiv
    exact Group.isSolvable_of_isSolvable_injective (f := e.left.toMonoidHom) e.left.injective
  | g2Full =>
    obtain ⟨e⟩ := h
    let := solvable_of_core_quotient ExceptionalModels.G2.fullFirstQuotientEquiv
    exact Group.isSolvable_of_isSolvable_injective (f := e.left.toMonoidHom) e.left.injective
  | tits =>
    obtain ⟨e⟩ := h
    let := solvable_of_core_quotient Tits.ExceptionalParabolics.FirstQuotient.coreQuotientEquiv
    exact Group.isSolvable_of_isSolvable_injective (f := e.left.toMonoidHom) e.left.injective
  | reeFull =>
    obtain ⟨e⟩ := h
    let := solvable_of_core_quotient Tits.ExceptionalParabolics.FullRee.firstCoreQuotientEquiv
    exact Group.isSolvable_of_isSolvable_injective (f := e.left.toMonoidHom) e.left.injective
  | m12 =>
    obtain ⟨e⟩ := h
    have hs : Group.IsSolvable (MathieuTwelve.P 0) := by
      rw [MathieuTwelve.P_eq_L]
      exact solvable_of_binary_quotient MathieuTwelve.local_calculations.1
    let := hs
    exact Group.isSolvable_of_isSolvable_injective (f := e.left.toMonoidHom) e.left.injective
  | autM12 =>
    obtain ⟨e⟩ := h
    have hs : Group.IsSolvable (AutMathieuTwelve.P 0) := by
      rw [AutMathieuTwelve.P_eq_L]
      exact solvable_of_binary_quotient AutMathieuTwelve.local_calculations.1
    let := hs
    let a := e.left.trans AutMathieuTwelve.ambientIso.left.symm
    exact Group.isSolvable_of_isSolvable_injective (f := a.toMonoidHom) a.injective

/-- No exceptional catalogue row marks the original pair, in either orientation.
The original source Sylow, full overlap and right factor are retained. -/
theorem LocalData.zeroCore_not_exceptional_parabolic
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) (k : ExceptionalModels.Case) :
    ¬ ExceptionalModels.ParabolicModel k (zeroCoreAmalgam L H B D R) ∧
      ¬ ExceptionalModels.ParabolicModel k (zeroCoreAmalgam L H B D R).reverse := by
  have hn := (d.zeroCore_mixed_solvability h hH c hd hz).2
  refine ⟨fun he => hn (Global.ExceptionalComparison.right_solvable k _ he), ?_⟩
  intro he
  by_cases hj : k = .j2
  · subst k
    obtain ⟨e⟩ := he
    apply d.zeroCore_no_small_normal_sylow_borel h hH c hd hz
      HallJanko.j2Model.S HallJanko.j2Model.toMarking.B HallJanko.j2Model.toMarking.S_le_B _ e.middle
    intro E hE heE
    exact (Sporadic.LeechRelated.J2.sylow_normal_elementary_card_le_four _ E hE heE).trans
      (by decide)
  by_cases ha : k = .autJ2
  · subst k
    obtain ⟨e⟩ := he
    apply d.zeroCore_no_small_normal_sylow_borel h hH c hd hz
      HallJanko.autJ2Model.S HallJanko.autJ2Model.toMarking.B
      HallJanko.autJ2Model.toMarking.S_le_B _ e.middle
    exact NormalSylowElementary.bound_equiv
      Sporadic.LeechRelated.J2.ExceptionalParabolics.extensionEquivAut.symm 8
      Sporadic.LeechRelated.J2.extension_sylow_normal_elementary_card_le_eight
      HallJanko.autJ2Model.S
  exact hn (exceptional_left_solvable k _ hj ha he)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
