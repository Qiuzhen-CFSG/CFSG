module

public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
public import CFSG.Quasithin.ChapterA.Section01.RankActions.ResidualActions.OddCore
public import Theory.GroupTheory.PGroupSelfCentralizingAction

/-!
# p-group automorphisms detected on the generalized Fitting subgroup

Generalized-Fitting normality and self-centralization specialize the
self-centralizing normal-subgroup action theorem to A.1.9. The final theorem
discharges the literal universal input used in the A.1.26 residual-action
argument, with its original embedded subgroup and relative normalizer.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.1.9,
printed p.21, and its application on pp.25–26.
-/

public section
namespace CFSG.Quasithin.ChapterA
open Subgroup Theory.GroupTheory

/-- A.1.9: a p-group normalizing Y with trivial p-core and centralizing F*(Y)
centralizes Y. -/
theorem lemma_A_1_9 {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (A Y : Subgroup G)
    (hA : IsPGroup p A) (hn : A ≤ normalizer (Y : Set G))
    (hcore : pCore p Y = ⊥)
    (hfix : A ≤ centralizer ((generalizedFitting Y).map Y.subtype : Set G)) :
    A ≤ centralizer (Y : Set G) :=
  centralizes_of_pGroup_of_selfCentralizing_normal A Y (generalizedFitting Y)
    hA hn hcore ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le hfix

/-- Discharges the A.1.9 input of the actual A.1.26 residual-action consumer. -/
theorem pGroupFStarCentralizationInput : RankActions.PGroupFStarCentralizationInput :=
  fun _G _ _ p _ A Y hA hn hcore hfix => lemma_A_1_9 p A Y hA hn hcore hfix

/-- In the A.1.26 application, fixing all odd prime cores forces a two-group
to fix the odd core; no generalized-Fitting action premise remains. -/
theorem centralizes_oddCore_of_centralizes_odd_pCores
    {G : Type*} [Group G] [Finite G] (V : Subgroup G) (hV : IsPGroup 2 V)
    (hc : ∀ (p : ℕ) [Fact p.Prime], Odd p →
      V ≤ centralizer (pCore p G : Set G)) :
    V ≤ centralizer (pPrimeCore 2 G : Set G) :=
  RankActions.centralizes_oddCore_of_pCores_and_fStarInput
    pGroupFStarCentralizationInput V hV hc

end CFSG.Quasithin.ChapterA
