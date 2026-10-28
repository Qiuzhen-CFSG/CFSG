module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionPreparation
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionUnitaryPlane
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.Catalogue
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# Excluding the exceptional amalgams in 5.2.6

Every fixed exceptional Green Book model has a solvable full right
parabolic. For the binary Lie and Mathieu rows this follows from their
actual binary linear core quotient. The full J₂ right parabolic has
quotient S₃ × C₃ over its two-core; adjoining the specified outer
involution preserves solvability and transports to Aut(J₂).

Both original source parabolics contain nontrivial perfect factors and
are nonsolvable. Hence all eight fixed catalogue rows, including the two
binary automorphism extensions, are impossible in either orientation.
This holds even at parabolic equivalence, so the weaker source convention
in the two Hall–Janko rows is respected. The whole overlap is retained.

These are the exceptional exclusions at the start of the proof of 5.2.6.
They do not assert exhaustive F.1.12 recognition or identify the ambient
completion; those obligations remain with qt-d-1222-rankone-generic-global.
Original uniqueness retains its independent producer.

Source: Aschbacher–Smith 5.2.6, printed pp.650–651, and the corrected
concrete F.1.12(I)(8–13) catalogue, printed pp.262–264 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook
namespace ExceptionalComparison

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

private theorem j2_right_solvable : Group.IsSolvable (HallJanko.j2Model.toMarking.P 1) := by
  rw [HallJanko.j2Model_P_one]
  open Sporadic.LeechRelated.J2.ExceptionalParabolics in
    obtain ⟨e⟩ := (PairNormalizer.p₂_core_and_quotient SecondParabolic.l₂_core_card).2
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  exact solvable_of_core_quotient e

private theorem autJ2_right_solvable : Group.IsSolvable (HallJanko.autJ2Model.toMarking.P 1) := by
  have hj : Group.IsSolvable (Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.p₂) := by
    rw [← HallJanko.j2Model_P_one]
    exact j2_right_solvable
  let := hj
  have he : Group.IsSolvable (HallJanko.extensionModel.toMarking.P 1) := by
    rw [HallJanko.extensionModel_P_one]
    open Sporadic.LeechRelated.J2.ExceptionalParabolics in
      let : Group.IsSolvable (Seed.p₂.map intoExtension) :=
        Group.isSolvable_of_surjective (intoExtension.subgroupMap_surjective Seed.p₂)
    exact Group.isSolvable_sup_of_normalizes _ _
      (zpowers_le.mpr Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap.outerElement_normalizes_p₂)
  let := he
  exact Group.isSolvable_of_isSolvable_injective
    (f := HallJanko.extensionAutAmalgamIso.right.symm.toMonoidHom)
    HallJanko.extensionAutAmalgamIso.right.symm.injective

/-- Each fixed exceptional catalogue row has a solvable full right parabolic.
Only parabolic equivalence is used, including in the two Hall--Janko rows. -/
theorem right_solvable {X B Y : Type*} [Group X] [Group B] [Group Y]
    (c : ExceptionalModels.Case) (α : RankTwoAmalgam X B Y)
    (h : ExceptionalModels.ParabolicModel c α) : Group.IsSolvable Y := by
  have htwo : Group.IsSolvable (PSL(2,ZMod 2)) :=
    Theory.PSL2.OuterSolvable.isSolvable_of_card_two (by simp)
  let := htwo
  cases c with
  | g2Derived =>
    obtain ⟨e⟩ := h
    let := solvable_of_core_quotient Atlas.G2.ExceptionalLocalQuotients.derivedSecondQuotientEquiv
    exact Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective
  | g2Full =>
    obtain ⟨e⟩ := h
    let := solvable_of_core_quotient ExceptionalModels.G2.fullSecondQuotientEquiv
    exact Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective
  | tits =>
    obtain ⟨e⟩ := h
    let : Group.IsSolvable (ReeF4.LargeLocalSeeds.LinearQuotient 0) :=
      Theory.PSL2.OuterSolvable.isSolvable_of_card_two (by simpa using ReeF4.field_card 0)
    have hs := solvable_of_core_quotient Tits.ExceptionalParabolics.secondLocalFactorCoreQuotientEquiv
    rw [Tits.ExceptionalParabolics.secondLocalFactor_eq] at hs
    let := hs
    exact Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective
  | reeFull =>
    obtain ⟨e⟩ := h
    let : Group.IsSolvable (ReeF4.LargeLocalSeeds.LinearQuotient 0) :=
      Theory.PSL2.OuterSolvable.isSolvable_of_card_two (by simpa using ReeF4.field_card 0)
    let := solvable_of_core_quotient Tits.ExceptionalParabolics.FullRee.secondCoreQuotientEquiv
    exact Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective
  | j2 =>
    obtain ⟨e⟩ := h
    let := j2_right_solvable
    exact Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective
  | autJ2 =>
    obtain ⟨e⟩ := h
    let := autJ2_right_solvable
    exact Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective
  | m12 =>
    obtain ⟨e⟩ := h
    have hs : Group.IsSolvable (MathieuTwelve.P 1) := by
      rw [MathieuTwelve.P_eq_L]
      exact solvable_of_binary_quotient MathieuTwelve.local_calculations.2.2.1
    let := hs
    exact Group.isSolvable_of_isSolvable_injective (f := e.right.toMonoidHom) e.right.injective
  | autM12 =>
    obtain ⟨e⟩ := h
    have hs : Group.IsSolvable (AutMathieuTwelve.P 1) := by
      rw [AutMathieuTwelve.P_eq_L]
      exact solvable_of_binary_quotient AutMathieuTwelve.local_calculations.2.2.2.2.1
    let := hs
    let a := e.right.trans AutMathieuTwelve.ambientIso.right.symm
    exact Group.isSolvable_of_isSolvable_injective (f := a.toMonoidHom) a.injective

end ExceptionalComparison

variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n) (hp : Group.IsPerfect R)
include d h hp

/-- Both orientations of every fixed exceptional row are impossible already
at parabolic equivalence, because both original parabolics are nonsolvable. -/
theorem Preparation.not_exceptional_parabolic_models (c : ExceptionalModels.Case) :
    let α := sourceParabolicAmalgam ![L,R] (sourceS L H)
    ¬ ExceptionalModels.ParabolicModel c α ∧
      ¬ ExceptionalModels.ParabolicModel c α.reverse := by
  exact ⟨fun he => d.parabolics_not_solvable h hp 1 (ExceptionalComparison.right_solvable c _ he),
    fun he => d.parabolics_not_solvable h hp 0 (ExceptionalComparison.right_solvable c _ he)⟩

/-- This uses the exact source equivalence convention: compatible amalgams
in six rows and parabolic equivalence in the two Hall--Janko rows. -/
theorem Preparation.not_exceptional_models (c : ExceptionalModels.Case) :
    let α := sourceParabolicAmalgam ![L,R] (sourceS L H)
    ¬ ExceptionalModels.IsModel c α ∧ ¬ ExceptionalModels.IsModel c α.reverse := by
  have hn := d.not_exceptional_parabolic_models h hp c
  exact ⟨fun he => hn.1 he.parabolic,fun he => hn.2 he.parabolic⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
