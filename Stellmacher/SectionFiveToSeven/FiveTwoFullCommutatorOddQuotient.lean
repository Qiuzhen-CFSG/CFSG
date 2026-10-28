module
public import Stellmacher.SectionFiveToSeven.Result5_2
public import Stellmacher.SectionFiveToSeven.HypothesisTwoSectionThree

/-!
# Odd-prime quotient of a full Baumann commutator

Under Hypothesis Two, suppose P₂ centralizes the omega-center of S and
K≤P₂ equals its commutator with B(S). Then K modulo its two-core is a
p-group for some odd prime p.

Centralization makes the omega-center normal in P₂, excluding the two
noncentral alternatives of (5.1). Thus S is the ambient Sylow and P₂ is
in the relevant P-star family. The initial reductions of (5.2) make P₂
solvable and K subnormal in its two-residual. The Section Three subnormal
quotient theorem then gives the asserted odd-prime quotient.

This is the quotient input for the R₁ centralizer comparison in Stellmacher
(9.3), Journal of Algebra 190 (1997), p.49, and the same argument used in
(6.4), p.32. The hypotheses are exactly the central branch and full
Baumann commutator conditions; no classification hypothesis is added.
Source: `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

/-- A full Baumann commutator in the central branch has an odd-prime
p-group quotient by its own two-core. -/
public theorem fiveTwo_full_commutator_odd_quotient
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2, omegaOneCenter S⁆ = ⊥)
    (K : Subgroup H) (hKP : K ≤ P2) (hKB : K = ⁅K, baumannIn S⁆) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPGroup p (K ⧸ pCore 2 K) := by
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
  exact SectionThree.subnormal_quotient_twoCore_is_odd_pGroup
    (S0 : Subgroup H) h.sectionThreeHypotheses P2 hPset hred.1 K hKsub

end Stellmacher.SectionsFiveToSeven
