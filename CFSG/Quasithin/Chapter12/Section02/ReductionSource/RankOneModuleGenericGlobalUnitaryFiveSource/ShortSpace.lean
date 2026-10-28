module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.ShortSpace
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# The marked U₅ three-space and fixed line in Chapter 12

The original chosen-module input and its full-normalizer marking select the
same short root as the ambient unique-fixed-coset theorem. The literal reduced
endpoint comparison now transports the orthogonal three-space and its entire
four-element fixed line into the residual centralizer of that root. Both
endpoint maps, the whole middle action and all extension range identities are
retained. The line is the full fixed subgroup of the prime-to-two residual
of C_L(t); the later full-local-stabilizer and two quotient arguments are
still required.

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

/-- The same marked short root has ambient unique fixed cosets and the
constructed residual orthogonal space, with its full fixed line. -/
theorem rankOne_unitaryFive_marked_short_geometry
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
        ∃ tL : L, tL.val = t.val ∧
        ∃ j : ShortSpace.centralizer U.form ≃* centralizer ({tL} : Set L),
          (∀ x, (j x).val.val = (a.comparison.left.symm (U.rightLocalEquiv x.val).val).val) ∧
          IsConj (a.comparison.left.symm U.longInvolution).val
            (j (ShortSpace.longMark U.form U.rightLeviTrace U.rightLeviTrace_spec)).val.val ∧
          UnitaryFiveShortSpace.Geometry U tL j := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  let r := D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc
  obtain ⟨a,ell,F,h0,h1,hD,hE,hl,hr,hm,t,ht,ht2,htS,hshort,hfix⟩ :=
    d.unitaryFive_marked_short_unique_cosets hi hH hp U hc r
  exact ⟨a,ell,F,h0,h1,hD,hE,hl,hr,hm,t,ht,ht2,htS,hshort,hfix,
    d.unitaryFive_short_geometry_at hi hH hp U hc r a F h0 t ht hshort⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
