module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.Apartment
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryCompletion.FiveGeometry

/-!
# Closed unitary apartments for the whole reduced module

The actual Chapter 12 source pair, with W = wholeReduced T L, inherits the
split-torus apartment closure in the full extension geometry. Both parameter
conventions and the complete outer factor remain intact. The fourth rotation
power lies in the whole middle and has square one; this does not assert PSU
recognition or GlobalExit.

Source: Aschbacher–Smith 5.3.1–4, F.4.10,16–17 and Chapter 12,
printed pp.658–659,279,282–283,795 of `refs/quasithin.pdf`.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Global.UnitaryCompletion
open ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Native rotation-defect control on the literal original normalizers. -/
theorem rankOne_unitary_closed_apartment (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm)
    (E : FourExtension m hm) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    1 < m ∧ n = 2*m ∧ ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := G),
      c.left.range ⊓ c.right.range = c.middle.range ∧ E.innerGenerated c = ⊤ ∧
      FourWeyl.rotation m hm E c ^ 4∈c.middle.range ∧
      FourWeyl.rotation m hm E c ^ 8=1 := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_closed_apartment hi hH hp m hm hc E he horder

/-- Native rotation-defect control on the literal original normalizers. -/
theorem rankOne_unitaryFive_closed_apartment (D : ChosenModule T L V)
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
      ∃ t : U.F, ∃ ht : t + U.form.conj t = 1,
        FiveWeyl.rotation U t ht E c ^ 4∈c.middle.range ∧
        FiveWeyl.rotation U t ht E c ^ 8=1 := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_closed_apartment hi hH hp U hc E he horder

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
