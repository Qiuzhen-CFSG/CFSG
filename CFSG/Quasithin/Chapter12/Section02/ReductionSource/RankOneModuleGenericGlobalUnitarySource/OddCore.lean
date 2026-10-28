module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.OddCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Four

/-!
# Original-module maximal-W odd-core and Bender application

Apply the prepared odd-core exclusion to the original whole-reduced module
and its named full-normalizer extension. The same maximal W has a full
normalizer with trivial odd core and a centerless quotient normal closure
in the Bender alternative, with its Borel and Sylow maps retained. Both
orientations, degree-two rows, q=4 and the whole quotient kernel remain.

Odd outer degree is still explicit. This establishes the odd-core and
cyclic-exclusion part of F.4.42, not its final perfect-actor contradiction
or the ambient order comparison. Source: Aschbacher–Smith F.4.42, p.296,
applied at 5.3/12.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The original chosen module supplies odd-core exclusion and the
centerless Bender alternative on its literal maximal-W quotient. -/
theorem rankOne_unitary_short_maximal_bender_of_odd_outer
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
    ∃ _hU : U ≤ center (centralizer ({t} : Set L)),
      Nat.card U = 2^m ∧ IsElementaryAbelian 2 U ∧
      let M := centralizer ({t.val} : Set G)
      let X := (normalizer (L : Set G)).subgroupOf M
      let U₀ := U.map (UnitarySource.shortCentralizerEmbedding L t)
      let t₀ := UnitarySource.shortCentralizerEmbedding L t
        ⟨t,mem_centralizer_singleton_iff.mpr rfl⟩
      normalizer (U₀ : Set M) = X ∧ (X ≠ ⊤ →
    ∃ W : Subgroup M, zpowers t₀ ≤ W ∧ W < U₀ ∧ ¬ normalizer (W : Set M) ≤ X ∧
      (∀ R : Subgroup M, W < R → R ≤ U₀ → normalizer (R : Set M) ≤ X) ∧
      let N := normalizer (W : Set M)
      pPrimeCore 2 N = ⊥ ∧
      let f := QuotientGroup.mk' (W.subgroupOf N)
      let V := (U₀.subgroupOf N).map f
      let Y := (X.subgroupOf N).map f
      V ≠ ⊥ ∧ Y ≠ ⊤ ∧ normalizer (V : Set (N ⧸ W.subgroupOf N)) = Y ∧
      IsElementaryAbelian 2 V ∧
      ∃ hnormal : (V.subgroupOf Y).Normal, letI := hnormal;
      (∀ v ∈ V, v ≠ 1 → ∃! q : (N ⧸ W.subgroupOf N) ⧸ Y, v • q = q) ∧
      (let K := normalClosure (V : Set (N ⧸ W.subgroupOf N))
       pPrimeCore 2 K = ⊥ ∧ center K = ⊥ ∧ IsQuasisimple K ∧ BenderSuzuki.IsSimpleBenderGroup (K ⧸ center K) ∧
           Y.comap K.subtype = normalizer (V.subgroupOf K : Set K) ∧
           BenderSuzuki.IsBorelSubgroup (Y.comap K.subtype) ∧
           ∃ S : Sylow 2 K, (S : Subgroup K) ≤ Y.comap K.subtype ∧
             V.subgroupOf K = (omega₁ S (p := 2)).map (S : Subgroup K).subtype) ∧
      Group.IsSolvable (Y ⧸ centralizer (V.subgroupOf Y : Set Y))) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_short_maximal_bender_of_odd_outer hi hH hp m hm hc
    (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc) hodd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
