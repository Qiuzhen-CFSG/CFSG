module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortTransport
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# The chosen module's marked short-root common centralizers

The literal whole-reduced-module input supplies the original prepared
comparison. Its short root is marked through both maps of the reduced
amalgam. The opposite full normalizer centralizer lies in N_G(L), and the
ambient centralizer of every original right-center root gives the same
common-centralizer bound. No additional transport or centralizer premise
is required. The degree-two rows, both orientations and q=4 are retained.

Source: Aschbacher–Smith F.4.42 and its 5.3/12.2 application, printed
pp.295,659,795 of `refs/quasithin.pdf`. Unique fixed cosets and the full
short-root centralizer bound remain subsequent source obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The actual whole-overlap marking supplies the ambient common-centralizer
bounds from the original chosen-module hypotheses. -/
theorem rankOne_unitary_short_root_common_centralizers
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] ((T : Subgroup G) ⊓ L)) (amalgam m hm).reverse,
      let t := (ChapterF.UnitarySource.FourShortTransport.sourceShort m hm e).val
      t ∈ L.pCoreIn 2 ∧ orderOf t = 2 ∧
      normalizer (residual H : Set G) ⊓ centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      ∀ z ∈ (center (residual H)).map (residual H).subtype, orderOf z = 2 →
        centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_short_root_common_centralizers hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
