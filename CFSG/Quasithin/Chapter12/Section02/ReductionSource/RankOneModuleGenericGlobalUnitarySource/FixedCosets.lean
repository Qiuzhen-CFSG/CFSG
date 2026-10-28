module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.FixedCosets
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Four

/-!
# Original unitary fixed cosets after outer transfer

The original whole-reduced-module input and the named full extension supply
ambient return fusion, unique fixed cosets, control of two-element fusion,
and the I.8.5 line-normalizer equality after F.4.38's odd outer degree.
The same short and long roots and entire q-element quotient kernel occur
throughout. The odd-degree premise, maximal-W part of F.4.42 and ambient
order comparison remain source obligations.

Source: Aschbacher–Smith F.4.38,42, pp.294–296, applied at 5.3/12.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Apply the full fixed-coset argument to the original chosen module,
retaining exactly the existing extension's odd-degree premise. -/
theorem rankOne_unitary_short_fixed_cosets_of_odd_outer
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (hodd : ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex
      (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc).extension.carrier) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
      z.val.val ∈ (center (residual H)).map (residual H).subtype ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      let X := UnitarySource.shortLineLocalQuotient L t U
      U ≤ V ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      (∃! q : centralizer ({t.val} : Set G) ⧸
          (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)),
        UnitarySource.shortCentralizerEmbedding L t z • q = q) ∧
      (∀ x y : centralizer ({t.val} : Set G),
        x.val ∈ normalizer (L : Set G) → y.val ∈ normalizer (L : Set G) →
        IsPGroup 2 (zpowers x) → IsConj x y →
        ∃ a : centralizer ({t.val} : Set G), a.val ∈ normalizer (L : Set G) ∧ a*x*a⁻¹ = y) ∧
      (∀ v ∈ V.map f, v ≠ 1 → ∃! q :
          (UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U) ⧸ X,
        v • q = q) ∧
      UnitarySource.shortLineNormalizer L t U =
        (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_short_fixed_cosets_of_odd_outer hi hH hp m hm hc
    (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc) hodd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
