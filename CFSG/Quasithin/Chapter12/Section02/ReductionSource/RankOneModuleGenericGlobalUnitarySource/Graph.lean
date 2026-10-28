module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.Graph
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# The original chosen-module graph-fixed unitary pair

The literal whole-reduced Chapter12 module supplies the original prepared
input with the complete KnownSimple catalogue. Its degree-two comparison
then produces a graph involution in the original ambient T, outside both
residual factors, and a compatible isomorphism of the whole fixed local
diagram with the symplectic diagram times its marked central graph C₂.
Both orientations and q=4 are retained, with m>1 and n=2m.

Source: Aschbacher–Smith F.4.37 and the applications in 5.3 and 12.2,
printed pp.293,659,795 of `refs/quasithin.pdf`. Ambient centralizer Sylow
placement, transfer and the full-normalizer extension remain further steps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The actual chosen whole-reduced module supplies the prepared graph-fixed
amalgam, including the original ambient T and the marked central graph factor. -/
theorem rankOne_unitary_graph_fixed_amalgam
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    1 < m ∧ n = 2*m ∧
      ∃ f : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        f.val ∈ sourceS L H ∧ f.val ∈ (T : Subgroup G) ∧ orderOf f.val = 2 ∧
        f.val ∉ L ∧ f.val ∉ residual H ∧
        ((∃ e : RankTwoAmalgam.Iso
          (centralizerDiagram (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) f)
          (ChapterF.UnitarySource.FourGraph.fixedDiagram m),
            e.middle (centralPoint f) = (1,Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter.generator)) ∨
         (∃ e : RankTwoAmalgam.Iso
          (centralizerDiagram (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) f)
          (ChapterF.UnitarySource.FourGraph.fixedDiagram m).reverse,
            e.middle (centralPoint f) = (1,Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter.generator))) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_graph_fixed_amalgam hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
