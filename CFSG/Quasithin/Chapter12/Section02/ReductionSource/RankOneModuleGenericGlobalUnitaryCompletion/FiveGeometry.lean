module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.FiveGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryCompletion

/-!
# The literal Chapter 12 PSU₅(4) normalizer completion

With W = wholeReduced T L, the genuine marked full extension and ambient
bound give quadrangle geometry, full order equality and generation by the
original normalizers. Simplicity also makes the native endpoint images
generate G. Both comparison orientations and the projective scalar kernel
are retained. The remaining F.4.17 identification is needed for GlobalExit.

Source: Aschbacher–Smith 5.3.1–4,F.4.13,17,24 and Chapter 12,
`refs/quasithin.pdf`, pp.658–659,280–283,287,795.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory SimpleGraph
open Subgroup.CosetGeometry.RankTwo
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Global.UnitaryCompletion
open ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Quadrangle geometry on the literal original normalizers, with W equal
to the whole reduced module and both fixed-model comparison orientations retained. -/
theorem rankOne_unitaryFive_completion_quadrangle (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : FiveLocalComparison L (residual H) (Global.sourceS L H) U)
    (E : FiveExtension U) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    n = 4 ∧
      ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
          (G := NormalizerJoin L (residual H)),
        c.left.range ⊓ c.right.range = c.middle.range ∧
        (∀ v (p : (graph c.cosetFamily).Walk v v), p.IsCycle → 8 ≤ p.length) ∧
        (∀ v w, (graph c.cosetFamily).dist v w ≤ 4) ∧
        (∃ v, ∃ p : (graph c.cosetFamily).Walk v v, p.IsCycle ∧ p.length = 8) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_completion_quadrangle hi hH hp U hc E he horder

/-- The literal whole-reduced-module application needs no extra generation
premise: the bound and quadrangle census force the original normalizers to
fill G, with the full extension order retained. -/
theorem rankOne_unitaryFive_normalizers_generate_and_card (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : FiveLocalComparison L (residual H) (Global.sourceS L H) U)
    (E : FiveExtension U) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    n = 4 ∧ NormalizerJoin L (residual H) = ⊤ ∧
      Nat.card G = Nat.card E.carrier := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_normalizers_generate_and_card hi hH hp U hc E he horder

/-- The original simple group is a faithful completion of the native
projective amalgam with the inherited endpoint maps and entire overlap. -/
theorem rankOne_unitaryFive_native_ambient_completion (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : FiveLocalComparison L (residual H) (Global.sourceS L H) U)
    (E : FiveExtension U) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    n = 4 ∧ ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := G),
      c.left.range ⊓ c.right.range = c.middle.range ∧ E.innerGenerated c = ⊤ ∧
      ∃ b : RankTwoAmalgam.FaithfulCompletion
          (SourceExtension.nativeAmalgam
            (P₀ := U.leftParabolic)
            (P₁ := U.rightParabolic)) (G := G),
        b.left = E.innerLeft c ∧ b.right = E.innerRight c ∧
        b.left.range ⊓ b.right.range = b.middle.range := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_native_ambient_completion hi hH hp U hc E he horder

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
