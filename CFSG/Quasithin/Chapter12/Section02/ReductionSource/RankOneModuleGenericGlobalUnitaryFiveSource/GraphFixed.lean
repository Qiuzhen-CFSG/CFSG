module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.GraphFixed
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# Native graph-fixed order on the chosen U₅(4) extension

The original chosen-module hypotheses construct Input on the whole reduced
module and the published full-normalizer marking. Apply the graph-fixed
calculation to precisely its stored extension and literal base homomorphism.
The graph-element equation is explicit; this companion does not select an
outer involution, prove S=T, or supply the ambient order premise of completion.

Source: Aschbacher--Smith F.4.37--38 and 12.2.22, printed pp.293--294,795.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
open Theory.SpecificGroups.UnitaryFive.GraphFixed
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The exact graph inner centralizer on the same extension constructed
from the original chosen-module row, retaining the graph-element equation. -/
theorem rankOne_unitaryFive_graph_inner_centralizer (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    let r := D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc
    ∀ f : r.extension.carrier, f.val=projectiveAut U.form U.matrix →
      let Cf := r.extension.baseHom.range ⊓ centralizer ({f} : Set r.extension.carrier)
      Nonempty (Cf ≃* Matrix.PSp4Three.Sp 2 (FixedBy.subfield U.F U.form.conj)) ∧
        Nat.card Cf=979200 ∧ ∀ P : Sylow 2 Cf, Nat.card P=256 := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  let r := d.unitaryFiveNormalizerMarking hi hH hp U hc
  exact fun f hf => r.graph_inner_centralizer f hf

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
