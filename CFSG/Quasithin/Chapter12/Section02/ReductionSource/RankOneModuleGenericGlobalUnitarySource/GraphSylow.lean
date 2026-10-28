module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.GraphSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# The chosen-module graph involution and its common fixed Sylow

The original whole-reduced module constructs a graph involution in sourceS
inside the original ambient T. Its centralizer in sourceS is simultaneously
Sylow in both source-parabolic centralizers, with order 2q⁴. Both fixed
amalgam maps, the whole overlap and the marked central graph kernel are
retained. The original residuals exclude the graph element, and m>1,
n=2m follow from the original nonsolvability hypotheses. Both degree-two
orientations include q=4.

Source: Aschbacher–Smith F.4.37 and its 5.3/12.2 application, printed
pp.293,659,795 of `refs/quasithin.pdf`. Promotion to the full ambient
centralizer, outer transfer and the full-normalizer realization remain
further obligations; sourceS is not substituted for T.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The original whole-reduced module supplies the actual common Sylow in
the two graph-fixed source parabolics, with both whole-overlap markings. -/
theorem rankOne_unitary_graph_local_sylow
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
        Nat.card (sourceS L H ⊓ centralizer ({f.val} : Set G) : Subgroup G) = 2*(2^m)^4 ∧
        (∀ i : Fin 2, ∃ Q : Sylow 2
          (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊓
            centralizer ({f.val} : Set G) : Subgroup G),
          (Q : Subgroup _).map
            (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊓
              centralizer ({f.val} : Set G)).subtype =
                sourceS L H ⊓ centralizer ({f.val} : Set G)) ∧
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
  exact d.unitary_graph_local_sylow hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
