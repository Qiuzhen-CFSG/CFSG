module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.GraphCenter
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.LongFixed
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# The chosen-module graph characteristic plane and fixed long-root obstruction

The literal wholeReduced input supplies the same degree-two graph actor,
its marked fixed diagram, and the q² characteristic plane in C_sourceS(f).
The separately selected outer centralizer has a larger ambient normalizer;
its two-group cannot preserve any nontrivial subgroup of the original
right residual center. No identification of these two actors is made.

Source: Aschbacher–Smith F.4.37 and 5.3.3, pp.293,659, with the original
Chapter12 hypotheses on p.795 (`refs/quasithin.pdf`).
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Theory.SpecificGroups Theory.SpecificGroups.ClassicalUnitary
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


omit hc in
theorem rankOne_unitaryFour_graph_characteristic_plane
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm).reverse)) :
    1 < m ∧ n = 2*m ∧
      ∃ f : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
        f.val ∈ Global.sourceS L H ∧ f.val ∈ (T : Subgroup G) ∧ orderOf f.val = 2 ∧
        f.val ∉ L ∧ f.val ∉ residual H ∧
        (∀ i : Fin 2, Chapter1.IsSylowIn 2
          (Global.sourceS L H ⊓ centralizer ({f.val} : Set G))
          (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i ⊓
            centralizer ({f.val} : Set G))) ∧
        ((∃ e : RankTwoAmalgam.Iso
          (centralizerDiagram (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) f)
          (ChapterF.UnitarySource.FourGraph.fixedDiagram m),
            e.middle (centralPoint f) = (1,UnitaryFourOuter.generator)) ∨
         (∃ e : RankTwoAmalgam.Iso
          (centralizerDiagram (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) f)
          (ChapterF.UnitarySource.FourGraph.fixedDiagram m).reverse,
            e.middle (centralPoint f) = (1,UnitaryFourOuter.generator))) ∧
        let P := Global.sourceS L H ⊓ centralizer ({f.val} : Set G)
        let Z := (center P ⊓ _root_.commutator P).map P.subtype
        Nonempty (P ≃* ((SymplecticFour.unipotent (F := PointLocal.FixedField m)) ×
          UnitaryFourOuter.C2)) ∧
        Nat.card Z = (2^m)^2 ∧ Z ≠ ⊥ ∧
        (∀ z ∈ Z, z^2=1) ∧
        Z ≤ ((T : Subgroup G) ⊓ L) ⊓ centralizer ({f.val} : Set G) ∧
        normalizer (P : Set G) ≤ normalizer (Z : Set G) ∧ f.val ∉ Z :=
  d.unitaryFour_graph_characteristic_plane
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he

omit hc in
theorem rankOne_unitaryFour_degreeTwo_long_root_obstruction
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm).reverse)) :
    ∃ f : T, orderOf f=2 ∧ f.val ∉ L ∧ f.val ∉ residual H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      ∃ V : Subgroup G, IsPGroup 2 V ∧
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) < V ∧
        V ≤ centralizer ({f.val} : Set G) ∧
        V ≤ normalizer (((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) : Set G) ∧
        (∀ i : Fin 2, ¬ V ≤ normalizer (![L,residual H] i : Set G)) ∧
        (∀ B : Subgroup G, B ≤ (center (residual H)).map (residual H).subtype →
          V ≤ normalizer (B : Set G) → B=⊥) ∧
        let P := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
        let Z := (center P ⊓ _root_.commutator P).map P.subtype
        let B := Z ⊓ (center (residual H)).map (residual H).subtype
        Z ≤ ((T : Subgroup G) ⊓ L) ⊓ centralizer ({f.val} : Set G) ∧
          V ≤ normalizer (Z : Set G) ∧
          (V ≤ normalizer (B : Set G) → B=⊥) :=
  d.unitaryFour_degreeTwo_long_root_obstruction
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
