module
public import Stellmacher.SectionFiveToSeven.SixFourPairCommutatorTransfer
public import Stellmacher.SectionFiveToSeven.Result5_4
public import Stellmacher.CentralizerInvolutionCore

/-!
# Centralization for the fixed local pair in Stellmacher (6.4)

Under the central-action branch of Hypothesis Two, let F₁ and F₂ have
common Sylow T with B(S) ≤ T ≤ S. Suppose both centralize a nonidentity
involution w of T, F₂ ≤ P₂, and O²(F₂)=[O²(F₂),B(S)]. Then O²(F₂)
centralizes [Ω₁(Z(S)),O²(F₁)].

The central involution lies in the two-core of L=F₁ join F₂ and in
Q=T intersect O₂(L), so both are nontrivial. The central branch of (5.1)
makes S the ambient Sylow and gives the PStar hypothesis. Choosing a
maximal two-local subgroup above N_H(S) supplies the auxiliary parameter
of (5.4), which puts Ω₁(Z(S)) in O₂(L). The pair-core normalizer theorem
puts L inside the two-local N_H(Q). Theorem (5.2) then makes O²(F₂)
subnormal in that normalizer, discharging the final premise of the
pair commutator transfer.

This supplies all structural premises for the first commutator paragraph
of Stellmacher (6.4), Journal of Algebra 190 (1997), p.32. Source:
`refs/files/stellmacher-n-group.pdf`. No supplied Sylow control beyond
actual family membership, or normality of the inner commutator, is assumed.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

public theorem sixFour_fixed_pair_centralization
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2, omegaOneCenter S⁆ = ⊥)
    (T F1 F2 : Subgroup H) (hBT : baumannIn S ≤ T) (hTS : T ≤ S)
    (hF1 : F1 ∈ PFamily ⊤ T) (hF2 : F2 ∈ PFamily ⊤ T)
    (hF2P : F2 ≤ P2) (w : H) (hwT : w ∈ T) (hw2 : w ^ 2 = 1) (hwne : w ≠ 1)
    (hF1w : F1 ≤ Subgroup.centralizer ({w} : Set H))
    (hF2w : F2 ≤ Subgroup.centralizer ({w} : Set H))
    (hKB : twoResidualAmbient F2 = ⁅twoResidualAmbient F2, baumannIn S⁆) :
    ⁅⁅omegaOneCenter S, twoResidualAmbient F1⁆, twoResidualAmbient F2⁆ = ⊥ := by
  have hZP : omegaOneCenter S ≤ P2 :=
    (Subgroup.map_subtype_le _).trans h.fiveOne.P2_mem.1.2.1.1
  have hZn : NormalIn (omegaOneCenter S) P2 := by
    refine ⟨hZP, (Subgroup.normal_subgroupOf_iff_le_normalizer hZP).mpr ?_⟩
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcase : S = (S0 : Subgroup H) ∧ P2 ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter S : Set H)) S := by
    cases h.fiveOne.alternative with
    | a _ _ hn => exact (hn hZn).elim
    | b hS hstar => exact ⟨hS,hstar⟩
    | c _ _ _ _ hn _ _ _ _ _ _ _ _ => exact (hn hZn).elim
  obtain ⟨hS,hstar⟩ := hcase
  let L := F1 ⊔ F2
  let Q := T ⊓ twoCoreAmbient L
  let U := Subgroup.normalizer (Q : Set H)
  let K := twoResidualAmbient F2
  have hTL : T ≤ L := hF1.1.2.1.1.trans le_sup_left
  have hLw : L ≤ Subgroup.centralizer ({w} : Set H) := sup_le hF1w hF2w
  have hwL : w ∈ L := hTL hwT
  have hwcore : w ∈ twoCoreAmbient L := central_involution_mem_twoCore L w hwL hLw hw2
  have hcore : twoCoreIn L ≠ ⊥ := by
    intro hb
    exact hwne (show w ∈ (⊥ : Subgroup H) from hb ▸ hwcore)
  have hQne : Q ≠ ⊥ := by
    intro hb
    exact hwne (show w ∈ (⊥ : Subgroup H) from hb ▸ (show w ∈ Q from ⟨hwT,hwcore⟩))
  have hQp : IsPGroup 2 Q := ((pCore_isPGroup (p := 2) (G := L)).map L.subtype).to_le inf_le_right
  have hUlocal : IsTwoLocal U := ⟨Q,hQne,hQp,rfl⟩
  have hLN : L ≤ U := SectionThree.pair_le_normalizer_inf_twoCoreAmbient T F1 F2 L
    hF1.1.2.1.2 hF2.1.2.1.2 rfl
  have hKsub : IsSubnormalIn K U := by
    have hstar0 : P2 ∈ PStarFamily
        (Subgroup.centralizer (omegaOneCenter (S0 : Subgroup H) : Set H))
        (S0 : Subgroup H) := hS ▸ hstar
    have hlocal0 : ∀ U : Subgroup H, IsTwoLocal U → baumannIn (S0 : Subgroup H) ≤ U →
        Group.IsSolvable U ∧ IsCharacteristicTwoType U := hS ▸ h.local_B
    have hKB0 : K = ⁅K,baumannIn (S0 : Subgroup H)⁆ := hS ▸ hKB
    have hBU : baumannIn (S0 : Subgroup H) ⊔ K ≤ U := by
      rw [← hS]
      exact sup_le (hBT.trans (hTL.trans hLN))
        ((Subgroup.map_subtype_le _).trans (le_sup_right.trans hLN))
    exact lemma_five_two S0 _ _ _ P2 K rfl rfl rfl hstar0
      ((Subgroup.map_subtype_le _).trans hF2P) hlocal0 hKB0 U hUlocal hBU
  have hS0ne : (S0 : Subgroup H) ≠ ⊥ := hS ▸ h.fiveOne.S_nontrivial
  let N := Subgroup.normalizer (S0 : Set H)
  have hNlocal : IsTwoLocal N := ⟨(S0 : Subgroup H),hS0ne,S0.isPGroup',rfl⟩
  obtain ⟨M,hNM,hMmax⟩ := Finite.exists_le_maximal hNlocal
  have hM : IsMaximalTwoLocalContaining (S0 : Subgroup H) M :=
    ⟨hMmax,(S0 : Subgroup H).le_normalizer.trans hNM⟩
  have hZcore := lemma_five_four S0 S P1 P2 h T F1 F2 L M ⟨hBT,hTS⟩
    hF1 hF2 rfl hM hcore (Or.inl hS)
  exact sixFour_pair_commutator_transfer h hcomm T F1 F2
    hF1.1.2.1.2 hF2.1.2.1.2 hBT hTS hF2P hQne hZcore hKB hKsub

end Stellmacher.SectionsFiveToSeven
