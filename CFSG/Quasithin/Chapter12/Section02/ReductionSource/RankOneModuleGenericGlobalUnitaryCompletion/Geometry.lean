module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.Geometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryCompletion

/-!
# The literal Chapter 12 unitary normalizer quadrangle

The whole-reduced-module input and prepared comparison supply m > 1 and
n = 2m. With the source producer's compatible full extension and ambient
order bound, the actual normalizer completion has girth eight and diameter
four. The exact quadrangle count then forces ambient generation and order
equality. This supplies the geometric and numerical steps of F.4.24; the
Hermitian group identification and GlobalExit still require proof.

Source: Aschbacher–Smith 5.3.1–4, F.4.13,24 and Chapter 12,
printed pp.658–659,280,287,795.
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
to the whole reduced module and both ordinary and degree-two orientations retained. -/
theorem rankOne_unitary_completion_quadrangle (D : ChosenModule T L V)
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
    1 < m ∧ n = 2*m ∧
      ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
          (G := NormalizerJoin L (residual H)),
        c.left.range ⊓ c.right.range = c.middle.range ∧
        (∀ v (p : (graph c.cosetFamily).Walk v v), p.IsCycle → 8 ≤ p.length) ∧
        (∀ v w, (graph c.cosetFamily).dist v w ≤ 4) ∧
        (∃ v, ∃ p : (graph c.cosetFamily).Walk v v, p.IsCycle ∧ p.length = 8) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_completion_quadrangle hi hH hp m hm hc E he horder

/-- The literal whole-reduced-module application needs no extra generation
premise: the bound and quadrangle census force the original normalizers to
fill G, with the full extension order retained. -/
theorem rankOne_unitary_normalizers_generate_and_card (D : ChosenModule T L V)
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
    1 < m ∧ n = 2*m ∧ NormalizerJoin L (residual H) = ⊤ ∧
      Nat.card G = Nat.card E.carrier := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_normalizers_generate_and_card hi hH hp m hm hc E he horder

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
