module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.ShortCentralizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# Full U₅ short-root centralizer containment in Chapter 12

The same original marking, whole-middle action and selected short root
satisfy both F.4.42 quotients. Their full ambient centralizer is contained
in the original plane normalizer, with no extra centralizer premise.

Source: Aschbacher–Smith 12.2.22 and F.4.42, printed pp.795,295–296.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open Theory.SpecificGroups.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The selected short root has its full ambient centralizer in the
original plane normalizer on the same extension marking. -/
theorem rankOne_unitaryFive_marked_short_centralizer
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    let r := D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc
    ∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse,
    ∃ ell : UnitaryNativeLift.Five.LiftReverse U a,
    ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
        r.extension.amalgam.reverse,
      (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
      (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
      (∀ z, (F.middle z).val = (ell.action z).val) ∧
      r.extension.carrier = inner U.Carrier ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp ell.action).range ∧
      r.extension.left = U.leftParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp ell.action).range ∧
      r.extension.right = U.rightParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp ell.action).range ∧
      r.extension.middle =
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp ell.action).range ∧
      ∃ t : (normalizerAmalgam L (residual H)).M₁₂,
        t.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ∧
        orderOf t.val=2 ∧ t.val ∈ sourceS L H ∧
        (F.middle t).val = MulAut.conj U.shortInvolution.val ∧
        (∀ z : G, z ∈ (center (residual H)).map (residual H).subtype → orderOf z=2 →
        ∀ x : centralizer ({t.val} : Set G), IsConj z x.val →
          ∃! q : centralizer ({t.val} : Set G) ⧸
            (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)), x • q=q) ∧
        centralizer ({t.val} : Set G) ≤ normalizer (L : Set G) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  let r := D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc
  obtain ⟨a,ell,F,h0,h1,hD,hE,hl,hr,hm,t,ht,ht2,htS,hshort,hfix⟩ :=
    d.unitaryFive_marked_short_unique_cosets hi hH hp U hc r
  exact ⟨a,ell,F,h0,h1,hD,hE,hl,hr,hm,t,ht,ht2,htS,hshort,hfix,
    d.unitaryFive_short_centralizer_at hi hH hp U hc r a F h0 h1 t ht ht2 hshort⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
