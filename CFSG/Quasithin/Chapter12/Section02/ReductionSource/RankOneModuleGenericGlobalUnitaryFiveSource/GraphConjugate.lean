module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.GraphConjugate
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# Conjugated graph fixed groups in the chosen U₅(4) row

Construct the whole-reduced Input and its original full-normalizer marking.
A conjugated graph equation then gives the inner fixed-group order on
that same extension, with explicit transport of every native subgroup.
In particular the two original parabolics and their overlap are retained.

Source: F.4.37 and 12.2.22, printed pp.293,795 of refs/quasithin.pdf.
The conjugating automorphism is still an explicit input, not a constructed
normal form for the selected outer involution.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
open Theory.SpecificGroups.UnitaryFive.GraphFixed
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Apply conjugated graph transport to the same constructed marking,
including the native endpoints and flag through its literal base map. -/
theorem rankOne_unitaryFive_conjugate_graph_inner_centralizer (D : ChosenModule T L V)
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
    ∀ (f : r.extension.carrier) (b : MulAut U.Carrier),
      f.val=b*projectiveAut U.form U.matrix*b⁻¹ →
      let Cf := r.extension.baseHom.range ⊓ centralizer ({f} : Set r.extension.carrier)
      Nonempty (Cf ≃* Matrix.PSp4Three.Sp 2 (FixedBy.subfield U.F U.form.conj)) ∧
        Nat.card Cf=979200 ∧ (∀ P : Sylow 2 Cf, Nat.card P=256) ∧
        ∀ P : Subgroup U.Carrier,
          ∃ e : (P.comap b.toMonoidHom ⊓ (projectiveAut U.form U.matrix).fixedSubgroup : Subgroup U.Carrier) ≃*
              (P.map r.extension.baseHom ⊓ centralizer ({f} : Set r.extension.carrier) : Subgroup r.extension.carrier),
            ∀ x, (e x).val=r.extension.baseHom (b x.val) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  let r := d.unitaryFiveNormalizerMarking hi hH hp U hc
  exact fun f b hf => r.conjugate_graph_inner_centralizer f b hf

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
