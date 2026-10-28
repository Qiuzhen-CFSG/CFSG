module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2OuterRootAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2OuterCentralizer

/-!
# The original Chapter 12 outer involution's small centralizer

Compatible conjugation on the original parabolics preserves the marked Hall
torus. The six-root calculation therefore discharges the root-action premise
in the q³ bound for C_S(t), giving |C_T(t)| < q⁴ for the same outer involution
and its original quotient field map. No additional action hypothesis remains.
Ambient centralizer Sylow placement is still required to deduce S=T.

Source: Aschbacher–Smith F.4.37–38, pp.293–294, and 5.3.3, p.659
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Subgroup.OddHall Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Atlas.G2 Atlas.G2.LieParabolicSetup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original marked outer involution has the strict centralizer bound;
the root action is now constructed from the two actual parabolic maps. -/
theorem rankOne_global_g2_outer_involution_centralizer_lt
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B Y : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hD : Y ≤ ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
        b.val ∈ Y ↔ (e.middle b).val ∈ splitTorus)
    (t : T) (ht2 : orderOf t=2) (htS : t.val ∉ Global.sourceS L H)
    (htD : t.val ∈ normalizer (Y : Set G)) :
    Nat.card (Global.sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≤ Nat.card F^3 ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) < Nat.card F^4 :=
  d.g2_outer_involution_centralizer_lt
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F e hD hmark t ht2 htS htD

/-- A proper original core supplies the same actual outer involution, torus
marking, order-two quotient field action and strict centralizer bound. -/
theorem rankOne_global_g2_exists_outer_involution_small_centralizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hne : Global.sourceS L H ≠ (T : Subgroup G)) :
    let C := ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H)
    ∃ Y : Subgroup G, Y ≤ C ∧ IsHallSubgroup oddPrimes (Y.subgroupOf C) ∧
      (∀ b : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
        b.val ∈ Y ↔ (e.middle b).val ∈ Atlas.G2.splitTorus) ∧
      ∃ eR : (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.Group F,
      ∃ t : T, orderOf t=2 ∧ t.val ∉ Global.sourceS L H ∧
        t.val ∈ normalizer (Y : Set G) ∧
        orderOf (Global.residualSylowFieldAction hH.1.1.2 eR t)=2 ∧
        Nat.card (Global.sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≤ Nat.card F^3 ∧
        Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) < Nat.card F^4 :=
  d.g2_exists_outer_involution_small_centralizer
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F e hne

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
