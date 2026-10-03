module
public import Stellmacher.SectionFiveToSeven.Result5_2
public import Stellmacher.SectionFiveToSeven.HypothesisTwoSectionThree
public import Theory.GroupTheory.SubnormalOddCoreActionOvergroup

/-!
# The repeated subnormal action transfer in Stellmacher (6.4)

In the branch where P2 centralizes the central involutions of S, let
K <= P2 satisfy K = [K,B(S)]. Suppose an elementary abelian two-subgroup A
is normal in a two-local subgroup U containing B(S) and K. If O2(K)
centralizes A, then K centralizes A.

The central branch of (5.1) forces S to be the distinguished ambient Sylow
and P2 to belong to PStar in the omega-center centralizer. The initial
reductions of (5.2) make K subnormal in O^2(P2), and (5.2) makes K subnormal
in U. The Section Three subnormal quotient theorem gives odd order modulo
O2(K), and the consequence of (3.5) makes K centralize Z(O2(K)). The
subnormal odd-core action criterion in the supplied overgroup U now kills
[A,K].

This is the common argument used first with [Omega1(Z(S)),O^2(F1)] and
then with V in Stellmacher (6.4), Journal of Algebra 190 (1997), p.32.
The caller must supply the indicated normality and core centralization;
the construction of those inputs remains in the local assembly.
Source: `refs/files/stellmacher-n-group.pdf` and
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

public theorem sixFour_subnormal_transfer
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2, omegaOneCenter S⁆ = ⊥)
    (K : Subgroup H) (hKP : K ≤ P2) (hKB : K = ⁅K, baumannIn S⁆)
    (U : Subgroup H) (hU : IsTwoLocal U) (hBU : baumannIn S ⊔ K ≤ U)
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hAU : A ≤ U) (hAn : (A.subgroupOf U).Normal)
    (hcore : ⁅A, twoCoreAmbient K⁆ = ⊥) : ⁅A, K⁆ = ⊥ := by
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
    | b hS hstar => exact ⟨hS, hstar⟩
    | c _ _ _ _ hn _ _ _ _ _ _ _ _ => exact (hn hZn).elim
  obtain ⟨rfl, hstar⟩ := hcase
  have hred := five_two_initial_reductions S0 P2 K hstar hKP h.local_B hKB
  have hKsub : IsSubnormalIn K (twoResidualAmbient P2) := hred.2.2.1
  have hPset := (pFamily_iff_pSet _ _ _).mp h.fiveOne.P2_mem
  have hOmega : ⁅omegaOneCenterAmbient (S0 : Subgroup H), twoResidualAmbient P2⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact bot_unique ((Subgroup.commutator_mono
      (Subgroup.map_subtype_le (twoResidualSubgroup P2)) le_rfl).trans_eq hcomm)
  have hcenter := SectionThree.subnormal_twoCore_center_centralizes_of_residual_omega_central
    (S0 : Subgroup H) h.sectionThreeHypotheses P2 hPset hred.1 hOmega K hKsub
  obtain ⟨p, hp, hp2, hpK⟩ := SectionThree.subnormal_quotient_twoCore_is_odd_pGroup
    (S0 : Subgroup H) h.sectionThreeHypotheses P2 hPset hred.1 K hKsub
  let _ : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (Nat.card (K ⧸ pCore 2 K)) := by
    obtain ⟨n, hn⟩ := hpK.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hsub := lemma_five_two S0 (omegaOneCenter (S0 : Subgroup H))
    (baumannIn (S0 : Subgroup H))
    (Subgroup.centralizer (omegaOneCenter (S0 : Subgroup H) : Set H))
    P2 K rfl rfl rfl hstar hKP h.local_B hKB U hU hBU
  exact Subgroup.commutator_eq_bot_of_subnormal_odd_core_action_in A K U
    hAU hsub.1 hAn hsub.2 hodd hcore hcenter

end Stellmacher.SectionsFiveToSeven
