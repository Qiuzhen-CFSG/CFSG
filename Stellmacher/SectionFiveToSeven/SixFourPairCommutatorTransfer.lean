module
public import Stellmacher.SectionFiveToSeven.SixFourNormalContainerTransfer
public import Stellmacher.SectionThree.PairCoreNormalizer
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# The first commutator transfer for the pair in Stellmacher (6.4)

Let F1 and F2 have a common Sylow two-subgroup T with B(S) <= T <= S,
and put L=F1 join F2, Q=T intersect O2(L), and K=O^2(F2). In the central
branch of Hypothesis Two, assume F2 <= P2, Q is nontrivial, Omega1(Z(S))
lies in O2(L), K=[K,B(S)], and K is subnormal in N(Q). Then K centralizes
[Omega1(Z(S)),O^2(F1)].

The common-Sylow core normalizer theorem puts L inside N(Q). Restricting
subnormality to L gives O2(K) <= O2(L), while normality of the residual
in F2 puts O2(K) inside O2(F2) and hence T. Thus O2(K) <= Q. The central
involutions of S lie in B(S), so they also lie in Q. Apply the normal
container transfer to Q inside the two-local subgroup N(Q); its normal
closure of Omega1(Z(S)) contains the required first commutator.

This supplies the first commutator paragraph in Stellmacher (6.4),
Journal of Algebra 190 (1997), p.32. The caller obtains the residual
Baumann equality and subnormality from (5.2), and omega-core containment
from (5.4); these inputs are explicit here.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (6.4), and the
corresponding full proof in `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

public theorem sixFour_pair_commutator_transfer
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2, omegaOneCenter S⁆ = ⊥)
    (T F1 F2 : Subgroup H)
    (hT1 : IsSylowSubgroupIn T F1) (hT2 : IsSylowSubgroupIn T F2)
    (hBT : baumannIn S ≤ T) (hTS : T ≤ S) (hF2 : F2 ≤ P2)
    (hQ : T ⊓ twoCoreAmbient (F1 ⊔ F2) ≠ ⊥)
    (hZcore : omegaOneCenter S ≤ twoCoreAmbient (F1 ⊔ F2))
    (hKB : twoResidualAmbient F2 = ⁅twoResidualAmbient F2, baumannIn S⁆)
    (hKsub : IsSubnormalIn (twoResidualAmbient F2)
      (Subgroup.normalizer (T ⊓ twoCoreAmbient (F1 ⊔ F2) : Set H))) :
    ⁅⁅omegaOneCenter S, twoResidualAmbient F1⁆, twoResidualAmbient F2⁆ = ⊥ := by
  let L := F1 ⊔ F2
  let Q := T ⊓ twoCoreAmbient L
  let U := Subgroup.normalizer (Q : Set H)
  let K := twoResidualAmbient F2
  have hLN : L ≤ U := SectionThree.pair_le_normalizer_inf_twoCoreAmbient
    T F1 F2 L hT1 hT2 rfl
  have hTF1 : T ≤ F1 := by
    obtain ⟨R, rfl⟩ := hT1
    exact Subgroup.map_subtype_le _
  have hTL : T ≤ L := hTF1.trans le_sup_left
  have hQU : Q ≤ U := Subgroup.le_normalizer
  have hQp : IsPGroup 2 Q :=
    ((pCore_isPGroup (p := 2) (G := L)).map L.subtype).to_le inf_le_right
  have hU : IsTwoLocal U := ⟨Q, hQ, hQp, rfl⟩
  have hKF2 : K ≤ F2 := Subgroup.map_subtype_le _
  have hKL : K ≤ L := hKF2.trans le_sup_right
  have hKnL : (K.subgroupOf L).IsSubnormal := by
    have hc := hKsub.2.comap (Subgroup.inclusion hLN)
    exact hc
  have hKcoreL : twoCoreAmbient K ≤ twoCoreAmbient L :=
    pCoreAmbient_mono_of_isSubnormalIn K L 2 hKL hKnL
  have hKnF2 : (K.subgroupOf F2).Normal := by
    change (((twoResidualSubgroup F2).map F2.subtype).subgroupOf F2).Normal
    rw [subgroupOf_map_subtype_eq]
    unfold twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal (fun N =>
      Subgroup.normal_iInf_normal (fun hN => hN.1))
  have hKcoreF2 : twoCoreAmbient K ≤ twoCoreAmbient F2 :=
    pCoreAmbient_mono_of_isSubnormalIn K F2 2 hKF2 hKnF2.isSubnormal
  have hcoreF2T : twoCoreAmbient F2 ≤ T := by
    obtain ⟨R, hR⟩ := hT2
    rw [← hR]
    exact Subgroup.map_mono ((pCore_isPGroup (p := 2) (G := F2)).le_sylow_of_normal R)
  have hKQ : twoCoreAmbient K ≤ Q := le_inf (hKcoreF2.trans hcoreF2T) hKcoreL
  have hZB : omegaOneCenter S ≤ baumannIn S := by
    intro z hz
    have hzS := (mem_omegaOneCenterAmbient_iff S z).mp hz
    refine ⟨hzS.1, ?_⟩
    change z ∈ Subgroup.centralizer (omegaOneCenter (elementaryAbelianMaxJ S) : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hJS : elementaryAbelianMaxJ S ≤ S := sSup_le fun _ hA => hA.1
    exact hzS.2.2 x ((Subgroup.map_subtype_le _).trans hJS hx)
  have hZQ : omegaOneCenter S ≤ Q := le_inf (hZB.trans hBT) hZcore
  have hBU : baumannIn S ⊔ K ≤ U := sup_le (hBT.trans (hTL.trans hLN)) hKsub.1
  have hQn : (Q.subgroupOf U).Normal := Subgroup.normal_in_normalizer
  have htransfer := sixFour_normal_container_transfer h hcomm K (hKF2.trans hF2) hKB
    U hU hBU Q hQU (inf_le_left.trans hTS) hQn hZQ hKQ
  let A0 := Subgroup.normalClosure ((omegaOneCenter S).subgroupOf U : Set U)
  let A := A0.map U.subtype
  have hZA : omegaOneCenter S ≤ A := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (hZQ.trans hQU)]
    exact Subgroup.map_mono Subgroup.le_normalClosure
  have hAn : (A.subgroupOf U).Normal := by
    change ((A0.map U.subtype).subgroupOf U).Normal
    rw [subgroupOf_map_subtype_eq]
    exact Subgroup.normalClosure_normal
  have hUA : U ≤ Subgroup.normalizer (A : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp hAn
  have hRA : twoResidualAmbient F1 ≤ Subgroup.normalizer (A : Set H) :=
    (Subgroup.map_subtype_le _).trans (le_sup_left.trans (hLN.trans hUA))
  have hcA : ⁅omegaOneCenter S, twoResidualAmbient F1⁆ ≤ A :=
    (Subgroup.commutator_mono hZA le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hRA)
  exact bot_unique ((Subgroup.commutator_mono hcA le_rfl).trans_eq htransfer)

end Stellmacher.SectionsFiveToSeven
