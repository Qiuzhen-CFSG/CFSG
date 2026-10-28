module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.GraphFlag
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# The fixed isotropic flag in the chosen U₅(4) row

Construct the original whole-reduced Input and its exact full-normalizer
marking. A middle involution represented by a unitary graph twist supplies
a descended isotropic line and plane over the four-element fixed field.
Their fixed parabolic groups transport through the same literal base map,
including the whole overlap. No replacement extension or conjugator
membership in that extension is required.

Source: F.4.29(2), F.4.37(2) and 12.2.22, printed pp.289,293,795 of
refs/quasithin.pdf. The selected abstract actor's unitary-twist
representation and the full fixed-Sylow root geometry remain unproved.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
open Theory.SpecificGroups.UnitaryFive
open GraphFixed Descent
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Descend the literal middle actor’s flag on the original chosen-module marking. -/
theorem rankOne_unitaryFive_unitary_twist_descended_flag (D : ChosenModule T L V)
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
    ∀ (f : r.extension.middle), f^2=1 →
      ∀ u : U.form.unitarySubgroup,
      f.val=unitaryConj U.form u*projectiveAut U.form U.matrix →
    ∃ v : U.form.unitarySubgroup,
      let b := unitaryConj U.form v
      let W₀ := (line U.F).comap (unitaryLinear U.form v).toLinearMap
      let W₁ := (plane U.F).comap (unitaryLinear U.form v).toLinearMap
      let V₀ := FixedFlag.coordinates U.form W₀
      let V₁ := FixedFlag.coordinates U.form W₁
      f.val=b*projectiveAut U.form U.matrix*b⁻¹ ∧
      (∀ x, U.form.conj ∘ x ∈ W₀ ↔ x ∈ W₀) ∧
      (∀ x, U.form.conj ∘ x ∈ W₁ ↔ x ∈ W₁) ∧
      FixedFlag.scalarSpan U.form V₀=W₀ ∧
      FixedFlag.scalarSpan U.form V₁=W₁ ∧
      V₀ ≤ V₁ ∧
      Module.finrank (FixedBy.subfield U.F U.form.conj) V₀=1 ∧
      Module.finrank (FixedBy.subfield U.F U.form.conj) V₁=2 ∧
      (∀ x y : V₁, dotProduct x.val y.val=0) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  let r := d.unitaryFiveNormalizerMarking hi hH hp U hc
  exact fun f hf2 u hf => unitary_twist_descended_flag U r.extension f hf2 u hf

/-- Apply the endpoint transport to the same conjugator, retaining the whole middle. -/
theorem rankOne_unitaryFive_conjugate_graph_endpoints (D : ChosenModule T L V)
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
    ∀ (f : r.extension.middle) (v : U.form.unitarySubgroup),
      f.val=unitaryConj U.form v*projectiveAut U.form U.matrix*(unitaryConj U.form v)⁻¹ →
      let b := unitaryConj U.form v
      let W₀ := (line U.F).comap (unitaryLinear U.form v).toLinearMap
      let W₁ := (plane U.F).comap (unitaryLinear U.form v).toLinearMap
      let j := inclusion (inf_le_left.trans r.extension.left_le : r.extension.middle ≤ r.extension.carrier)
      ∃ e : (projectiveAut U.form U.matrix).fixedSubgroup ≃*
          (r.extension.baseHom.range ⊓ centralizer ({j f} : Set r.extension.carrier) : Subgroup r.extension.carrier),
        (∀ x, (e x).val=r.extension.baseHom (b x.val)) ∧
        (∀ x, (e x).val∈r.extension.family false ↔ x.val∈parabolic U.form W₀) ∧
        (∀ x, (e x).val∈r.extension.family true ↔ x.val∈parabolic U.form W₁) ∧
        (∀ x, (e x).val∈r.extension.middle.subgroupOf r.extension.carrier ↔
          x.val∈parabolic U.form W₀ ⊓ parabolic U.form W₁) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  let r := d.unitaryFiveNormalizerMarking hi hH hp U hc
  exact fun f v hg => unitary_conjugate_graph_endpoints U r.extension f v hg

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
