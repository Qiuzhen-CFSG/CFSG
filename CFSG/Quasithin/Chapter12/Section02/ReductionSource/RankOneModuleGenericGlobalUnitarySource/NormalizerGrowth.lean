module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.NormalizerGrowth
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# Chosen-module unitary outer centralizers and normalizer growth

The literal wholeReduced input supplies the ambient fusion, weak closure
and common inner Sylow used in the outer-centralizer argument. A fully
centralized involution lies in the original two-core. Maximizing an outer
centralizer gives one Sylow in both full endpoint centralizers and a
strictly larger ambient two-normalizer escaping both endpoints.

The degree-two row supplies this configuration without an outer-existence
premise. Its original graph element also retains the fixed-amalgam marking
and source-local Sylows, separately from the maximal choice. Both
orientations and q=4 are included. The native fixed-root geometry and
ordinary even-degree parity remain required for unconditional recognition.

Source: Aschbacher–Smith F.4.37–38 and 5.3.3, printed pp.293–294,659, with
the original Chapter12 input on p.795 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
open Chapter6.Source.RankOneGeneric.Global.UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}
variable (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm)
include D h hmany hn hpsl hH d hp hm hc


theorem rankOne_unitaryFour_fully_centralized_involution_mem_core
    (f : T) (hf : orderOf f=2)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
      (centralizer ({f.val} : Set G))) : f.val ∈ L.pCoreIn 2 :=
  d.unitaryFour_fully_centralized_involution_mem_core
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc f hf hs

theorem rankOne_unitaryFour_outer_centralizer_not_sylow
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ L) :
    ¬ Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
      (centralizer ({f.val} : Set G)) :=
  d.unitaryFour_outer_centralizer_not_sylow
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc f hf ho

theorem rankOne_unitaryFour_outer_centralizer_normalizer_growth
    (hex : ∃ f : T, orderOf f=2 ∧ f.val ∉ L) :
    ∃ f : T, orderOf f=2 ∧ f.val ∉ L ∧ f.val ∉ residual H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      ∃ V : Subgroup G, IsPGroup 2 V ∧
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) < V ∧
        V ≤ centralizer ({f.val} : Set G) ∧
        V ≤ normalizer (((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) : Set G) ∧
        ∀ i : Fin 2, ¬ V ≤ normalizer (![L,residual H] i : Set G) :=
  d.unitaryFour_outer_centralizer_normalizer_growth
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc hex

theorem rankOne_unitaryFour_centralizer_derived_center
    (f : T) :
    let P := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
    let Z := (center P ⊓ _root_.commutator P).map P.subtype
    Z ≤ ((T : Subgroup G) ⊓ L) ⊓ centralizer ({f.val} : Set G) ∧
      normalizer (P : Set G) ≤ normalizer (Z : Set G) :=
  d.unitaryFour_centralizer_derived_center
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc f

omit hc in
theorem rankOne_unitaryFour_graph_centralizer_not_sylow
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm).reverse)) :
    1 < m ∧ n = 2*m ∧
      ∃ f : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
        f.val ∈ Global.sourceS L H ∧ f.val ∈ (T : Subgroup G) ∧ orderOf f.val = 2 ∧
        f.val ∉ L ∧ f.val ∉ residual H ∧
        Nat.card (Global.sourceS L H ⊓ centralizer ({f.val} : Set G) : Subgroup G) = 2*(2^m)^4 ∧
        (∀ i : Fin 2, Chapter1.IsSylowIn 2
          (Global.sourceS L H ⊓ centralizer ({f.val} : Set G))
          (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i ⊓
            centralizer ({f.val} : Set G))) ∧
        ¬ Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
          (centralizer ({f.val} : Set G)) ∧
        ((∃ e : RankTwoAmalgam.Iso
          (centralizerDiagram
            (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) f)
          (ChapterF.UnitarySource.FourGraph.fixedDiagram m),
            e.middle (centralPoint f) =
              (1,Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter.generator)) ∨
         (∃ e : RankTwoAmalgam.Iso
          (centralizerDiagram
            (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) f)
          (ChapterF.UnitarySource.FourGraph.fixedDiagram m).reverse,
            e.middle (centralPoint f) =
              (1,Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter.generator))) :=
  d.unitaryFour_graph_centralizer_not_sylow
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he

omit hc in
theorem rankOne_unitaryFour_degreeTwo_normalizer_growth
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm).reverse)) :
    1 < m ∧ n = 2*m ∧
    ∃ f : T, orderOf f=2 ∧ f.val ∉ L ∧ f.val ∉ residual H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      ∃ V : Subgroup G, IsPGroup 2 V ∧
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) < V ∧
        V ≤ centralizer ({f.val} : Set G) ∧
        V ≤ normalizer (((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) : Set G) ∧
        (∀ i : Fin 2, ¬ V ≤ normalizer (![L,residual H] i : Set G)) ∧
        let P := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
        let Z := (center P ⊓ _root_.commutator P).map P.subtype
        Z ≤ ((T : Subgroup G) ⊓ L) ⊓ centralizer ({f.val} : Set G) ∧
          V ≤ normalizer (Z : Set G) :=
  d.unitaryFour_degreeTwo_normalizer_growth
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
