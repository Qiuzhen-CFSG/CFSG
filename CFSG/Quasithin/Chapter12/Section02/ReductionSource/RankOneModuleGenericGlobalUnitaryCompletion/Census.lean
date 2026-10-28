module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.Census
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryCompletion

/-!
# The four-walk census on the original Chapter 12 normalizer pair

The chosen whole-reduced-module input supplies the actual generic preparation.
Its ordinary or degree-two unitary comparison fixes m > 1 and n = 2m. The
compatible full-normalizer realization and ambient order bound then yield
unequal native valencies, numerical coset bounds, and a collision of distinct
nonbacktracking four-walks. No ambient-generation premise is required.

Source: Aschbacher–Smith 5.3.1–4, F.4.24 and the Chapter 12 application,
printed pp.658–659, 287 and795. Geodesicity and Hermitian recognition remain
necessary before this census gives smallness or a GlobalExit.
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

/-- Counting on the literal original normalizers, with W equal to the whole
reduced module and both ordinary and degree-two orientations retained. -/
theorem rankOne_unitary_completion_four_path_collision (D : ChosenModule T L V)
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
        (∀ i : Bool, Nat.card (NormalizerJoin L (residual H) ⧸ c.cosetFamily i) ≤
          fourCosetCount m i) ∧
        (∀ v : Vertex c.cosetFamily,
          Nat.card ((graph c.cosetFamily).neighborSet v) = fourDegree m v.type) ∧
        ∃ p q : BasedWalk (graph c.cosetFamily) 4 (base c.cosetFamily false),
          p.Nonbacktracking ∧ q.Nonbacktracking ∧ p.endpoint = q.endpoint ∧ p ≠ q := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_completion_four_path_collision hi hH hp m hm hc E he horder

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
