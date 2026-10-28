module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.CommonCentralizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# Common ambient centralizers in the chosen U₅(4) row

Construct the original Input on the whole reduced module and apply the
common-centralizer theorem to the marking of that same row. It supplies
the short marker in the whole overlap, all endpoint and range equations,
control of long-root line subgroup normalizers inside C_G(t), and literal
common-centralizer order transport through the same full endpoint map.
The result includes conjugates by the local short centralizer and retains
the full proper-K/KnownSimple hypotheses. All ambient involution centralizers
have trivial odd core by the separate long-root four-group argument.

This is the common-centralizer input to F.4.42 at 12.2.22, not the remaining
ambient short-centralizer equality or the same-extension order bound.
Source: Aschbacher--Smith F.4.42 and 12.2.22, printed pp.295--296,795.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Full common-centralizer and root-normalizer control for the marked
short involution of the original chosen-module row. -/
theorem rankOne_unitaryFive_marked_short_root_control (D : ChosenModule T L V)
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
    ∃ f : UnitaryNativeLift.Five.LiftReverse U a,
    ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
        r.extension.amalgam.reverse,
      (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
      (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
      (∀ z, (F.middle z).val = (f.action z).val) ∧
      r.extension.carrier = inner U.Carrier ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.left = U.leftParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.right = U.rightParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.middle =
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      ∃ t : (normalizerAmalgam L (residual H)).M₁₂,
        t.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ∧
        orderOf t.val = 2 ∧ t.val ∈ sourceS L H ∧
        (center (residual H)).map (residual H).subtype ≤
          normalizer (L : Set G) ⊓ centralizer ({t.val} : Set G) ∧
        pPrimeCore 2 (centralizer ({t.val} : Set G)) = ⊥ ∧
        (F.middle t).val = MulAut.conj U.shortInvolution.val ∧
        centralizer ({inclusion (inf_le_left.trans r.extension.left_le) (F.middle t)} :
          Set r.extension.carrier) ≤ r.extension.right.subgroupOf r.extension.carrier ∧
        Nat.card (centralizer ({inclusion inf_le_left t} : Set (normalizer (L : Set G)))) =
          Nat.card (centralizer ({inclusion (inf_le_left.trans r.extension.left_le) (F.middle t)} :
            Set r.extension.carrier)) ∧
        (normalizer (residual H : Set G) ⊓ centralizer ({t.val} : Set G) ≤
          normalizer (L : Set G)) ∧
        (∀ B : Subgroup G, B ≤ (center (residual H)).map (residual H).subtype → B ≠ ⊥ →
          normalizer (B : Set G) ⊓ centralizer ({t.val} : Set G) ≤
            normalizer (L : Set G) ⊓ centralizer ({t.val} : Set G)) ∧
        (∀ z : G, z ∈ (center (residual H)).map (residual H).subtype → z ≠ 1 →
          centralizer ({z} : Set G) ⊓ centralizer ({t.val} : Set G) ≤
            (normalizerAmalgam L (residual H)).M₁₂) ∧
        (∀ g ∈ normalizer (L : Set G) ⊓ centralizer ({t.val} : Set G),
          ∀ B : Subgroup G,
            B ≤ ((center (residual H)).map (residual H).subtype).map (MulAut.conj g).toMonoidHom →
            B ≠ ⊥ → normalizer (B : Set G) ⊓ centralizer ({t.val} : Set G) ≤
              normalizer (L : Set G) ⊓ centralizer ({t.val} : Set G)) ∧
        (∀ g ∈ normalizer (L : Set G) ⊓ centralizer ({t.val} : Set G),
          ∀ z : G,
            z ∈ ((center (residual H)).map (residual H).subtype).map (MulAut.conj g).toMonoidHom →
            z ≠ 1 → centralizer ({z} : Set G) ⊓ centralizer ({t.val} : Set G) ≤
              normalizer (L : Set G) ⊓ centralizer ({t.val} : Set G)) ∧
        (∀ z : normalizer (residual H : Set G),
          z.val ∈ (center (residual H)).map (residual H).subtype → z.val ≠ 1 →
          Nat.card (centralizer ({z.val} : Set G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) =
            Nat.card (centralizer ({F.right z} : Set r.extension.left) ⊓
              centralizer ({F.right (inclusion inf_le_right t)} : Set r.extension.left) :
                Subgroup r.extension.left)) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_marked_short_root_control hi hH hp U hc
    (D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc)

/-- Every ambient involution centralizer in the original chosen-module row
has trivial odd core, without assuming S=T or an ambient order comparison. -/
theorem rankOne_unitaryFive_involution_centralizer_oddCore (D : ChosenModule T L V)
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
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (x : G) (hx : orderOf x = 2) :
    pPrimeCore 2 (centralizer ({x} : Set G)) = ⊥ := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_involution_centralizer_oddCore hi hH hp U hc x hx

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
