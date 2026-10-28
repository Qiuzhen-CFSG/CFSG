module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Nonfusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Marked
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# Original chosen-module applications of the U₅(4) Thompson and fusion argument

The original many-overgroups row constructs Input on the whole reduced module.
The ambient Thompson identity, normalizer control and nonconjugate involutions
then require no additional action or fusion assumptions. The second application
uses the published marking of this exact chosen row and keeps its endpoint and
whole-normalizer equations while transporting full long-root centralizer orders
into the same extension endpoints. Full-extension centralizer placement,
outer transfer, F.4.42 and the final ambient order bound remain separate steps.
Source: Aschbacher–Smith F.4.35 and F.4.43, pp.292,296, applied at 12.2.22.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Stellmacher
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The full ambient Thompson and fusion conclusions on the original row. -/
theorem rankOne_unitaryFive_thompson_fusion (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam.reverse)) :
    let Z := (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype
    elementaryAbelianMaxJ (T : Subgroup G) = Z ∧
      normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) = normalizer (L : Set G) ∧
      (∀ x ∈ Z, ∀ y ∈ Z, IsConj x y → ∃ g ∈ normalizer (L : Set G), g*x*g⁻¹ = y) ∧
      (∃ x ∈ Z, ∃ y ∈ Z, orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.unitaryFive_thompson hi hH hp U hc,
    d.unitaryFive_thompson_normalizer hi hH hp U hc,
    fun _ hx _ hy hxy => d.unitaryFive_plane_center_fusion hi hH hp U hc hx hy hxy,
    d.unitaryFive_two_nonconjugate_involutions hi hH hp U hc⟩

/-- Full long-root centralizer orders transported by the published marking
of this same whole-reduced chosen row. -/
theorem rankOne_unitaryFive_marked_long_centralizers (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam.reverse)) :
    let r := D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc
    (∃ a : Global.UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam,
      ∃ f : Global.UnitaryNativeLift.Five.Lift U a,
      ∃ F : RankTwoAmalgam.Iso (Global.UnitaryCompletion.normalizerDiagram L (residual H))
          r.extension.amalgam,
        (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
        (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
        (∀ z, (F.middle z).val = (f.action z).val) ∧
        (∀ z : normalizer (residual H : Set G),
          z.val ∈ (center (residual H)).map (residual H).subtype → orderOf z.val = 2 →
          Nat.card (centralizer ({z.val} : Set G)) =
            Nat.card (centralizer ({F.right z} : Set r.extension.right)))) ∨
    (∃ a : Global.UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse,
      ∃ f : Global.UnitaryNativeLift.Five.LiftReverse U a,
      ∃ F : RankTwoAmalgam.Iso (Global.UnitaryCompletion.normalizerDiagram L (residual H))
          r.extension.amalgam.reverse,
        (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
        (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
        (∀ z, (F.middle z).val = (f.action z).val) ∧
        (∀ z : normalizer (residual H : Set G),
          z.val ∈ (center (residual H)).map (residual H).subtype → orderOf z.val = 2 →
          Nat.card (centralizer ({z.val} : Set G)) =
            Nat.card (centralizer ({F.right z} : Set r.extension.left)))) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_marked_long_centralizers hi hH hp U hc
    (D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
