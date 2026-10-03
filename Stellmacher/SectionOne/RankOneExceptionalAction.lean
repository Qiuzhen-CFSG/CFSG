module

public import Stellmacher.SectionOne.ExceptionalSmallMActionData
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.LocalCardThree
public import Stellmacher.SectionOne.ExceptionalOddActionKernel
public import Theory.GroupAction.CentralCoprimeKernel
public import Stellmacher.SectionOne.ExceptionalOddCentralizer
public import Stellmacher.SectionOne.ExceptionalOddCoreInvariant
public import Stellmacher.SectionOne.ExceptionalOddCoreCard
public import Stellmacher.SectionOne.ExceptionalFullCommutator
public import Stellmacher.SectionOne.ExceptionalNonquadratic

/-!
# Bounded exceptional action conclusions

This assembly treats failure of local genericity under the explicit bound
m(S)≤2 and the minimal-m hypothesis. The normalized local calculation
forces m(S)=2, |S|=4 and a sixteen-element commutator module U.
Local recursion gives order-three local commutators; their centralizer
calculation makes C_W(U) central, and coprime faithfulness kills it.
The fixed-line theorem then kills C_W(S), and the center-module transfer
proves actual W-invariance of U. The faithful GL4 action gives |W|=9
and abelianness, so the full commutator is U. The independently proved
nonquadratic transport supplies the last action conclusion.

The separate finite-group classification identifies G with SL2(2)² in
the final exceptional wrapper. This is a bounded theorem, not a proof of
the audited false unrestricted m(S)=2 assertion in Stellmacher (1.6)(b).
Source: `refs/latex/stellmacher-n-group.tex`, journal p.18.
-/

open scoped IsMulCommutative
namespace Stellmacher.SectionOne
open RankOneThreeGroupAssembly
universe u

public theorem rank_one_exceptional_small_m_action_conclusions
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS : IsElementaryAbelian 2 (S : Subgroup G))
    (hW : oddCore G = ⁅oddCore G, (S : Subgroup G)⁆)
    (hWthree : IsPGroup 3 (oddCore G))
    (hmin : ∀ Y : Subgroup G, Y ≤ (S : Subgroup G) → Y ≠ ⊥ →
      m (G := G) (V := V) (S : Subgroup G) ≤ m (G := G) (V := V) Y)
    (hlocal : RankOneAssemblyLocalHypothesis (G := G) (V := V) (S : Subgroup G))
    (hnongeneric : ¬ RankOneAssemblyGenericHypothesis (G := G) (V := V) (S : Subgroup G))
    (hm : m (G := G) (V := V) (S : Subgroup G) ≤ 2) :
    m (G := G) (V := V) (S : Subgroup G) = 2 ∧
      Nat.card (S : Subgroup G) = 4 ∧ Nat.card (oddCore G) = 9 ∧
      Nat.card (commutatorAction (oddCore G) V) = 16 ∧
      vStarAction₂ (G := G) (V := V) (S : Subgroup G) ≠ ⊥ := by
  obtain ⟨hmEq, hScard, F, hFW, hFcard, hnorm, hUcard, _hSkernel,
    hfixed, _hcover, hcomm⟩ :=
    exists_exceptional_small_m_normalized_action_data (S : Subgroup G) hS hnongeneric hmin hm
  let W : Subgroup G := oddCore G
  let U : Subgroup V := commutatorAction F V
  let Q : Subgroup G := W ⊓ fixingSubgroup G (U : Set V)
  have hlocal3 := local_commutator_card_three_of_card_four h (S : Subgroup G)
    hS hScard hlocal
  obtain ⟨hQS, hQW⟩ := exceptional_odd_action_kernel_centralizes
    h S hS hScard hW hlocal3 F hnorm hcomm
  have hQodd : Nat.Coprime 2 (Nat.card Q) :=
    (pPrimeCore_coprime_card (G := G) (p := 2)).of_dvd_right
      (Subgroup.card_dvd_of_le (show Q ≤ oddCore G from inf_le_left))
  have hcopQV : Nat.Coprime (Nat.card Q) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hn]
    exact hQodd.symm.pow_right n
  have hQfix : Q ≤ fixingSubgroup G (commutatorAction (S : Subgroup G) V : Set V) := by
    intro q hq
    rw [mem_fixingSubgroup_iff]
    intro v hv
    exact (mem_fixingSubgroup_iff (M := G) (s := (U : Set V))).mp hq.2 v (hcomm hv)
  have hQbot : Q = ⊥ := eq_bot_of_central_coprime_fixing_commutator
    W (S : Subgroup G) Q inf_le_left hW hQW hQS hcopQV hQfix h.action_faithful
  have hSp : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  have hCWS := oddCore_centralizer_eq_bot_of_fixed_card_two
    (S : Subgroup G) F hSp hnorm hfixed hQbot
  have hSnorm : (S : Subgroup G) ≤ Subgroup.normalizer (F : Set G) :=
    le_sup_left.trans hnorm
  let _ : IsInvariant (oddCore G) V U :=
    commutatorAction_isInvariant_oddCore_of_exceptional_data h (S : Subgroup G) F
      hSp hWthree hFW hFcard hSnorm hfixed hcomm hCWS
  obtain ⟨hWcard, hWcomm⟩ := oddCore_card_nine_of_faithful_sixteen_action
    h S hS hScard hWthree U hUcard hQbot
  let _ : IsMulCommutative (oddCore G) := hWcomm
  have hfull := commutatorAction_oddCore_eq_of_exceptional_data
    (V := V) (S : Subgroup G) F hW hFW hFcard hSnorm hcomm
  refine ⟨hmEq, hScard, hWcard, ?_, vStarAction₂_ne_bot_of_nongeneric (S : Subgroup G) hS hnongeneric⟩
  rw [hfull]
  exact hUcard

end Stellmacher.SectionOne

