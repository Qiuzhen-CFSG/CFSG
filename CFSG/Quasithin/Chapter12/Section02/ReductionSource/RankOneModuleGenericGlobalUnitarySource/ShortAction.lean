module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# The original chosen module and the short-quotient perfect action

The whole-reduced-module input constructs the same marked roots, full-line
quotient and actual perfect vector actor. The I.8.5 application excludes a
proper line-normalizer quotient once the marked unique fixed coset is proved.
Both comparison orientations, degree-two rows, q=4 and n=2m are retained.
This conditional application does not assert the full F.4.42 containment.
Source: Aschbacher–Smith F.4.42 and 5.3/12.2, printed pp.295–296,659,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The actual perfect quotient action and its precise I.8.5 application,
with the remaining ambient unique-fixed-coset premise displayed. -/
theorem rankOne_unitary_short_quotient_perfect_action
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
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
      z.val.val ∈ (center (residual H)).map (residual H).subtype ∧
      centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤
        normalizer (L : Set G) ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      let X := UnitarySource.shortLineLocalQuotient L t U
      U ≤ V ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      V.map f ≤ X ∧ ((V.map f).subgroupOf X).Normal ∧
      (∃ P : Subgroup (UnitarySource.shortLineNormalizer L t U ⧸
          UnitarySource.shortLineKernel L t U), Group.IsPerfect P ∧ P ≤ X ∧
        ∀ v ∈ V.map f, v ≠ 1 → ∃ a ∈ P, a * f z * a⁻¹ = v) ∧
      ((∃! q : centralizer ({t.val} : Set G) ⧸
          (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)),
          UnitarySource.shortCentralizerEmbedding L t z • q = q) →
        UnitarySource.shortLineNormalizer L t U ≤
          (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G))) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_short_quotient_perfect_action hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
