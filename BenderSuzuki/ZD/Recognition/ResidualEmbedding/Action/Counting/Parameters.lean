module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Reduction
import Theory.GroupTheory.ZStar.CoreFree

/-!
# The nontrivial odd counting parameter

The centralizer of a distinguished two-central involution contains an ambient
Sylow two-subgroup, so its index in `M` is odd. In the simple reduction that
index exceeds one: otherwise unique conjugate membership makes the involution
weakly closed in a Sylow subgroup, and the core-free Z-star theorem makes it
central in `G`, contradicting the properness of `M`.

An odd prime divisor then supplies the nontrivial prime share used in (6A).
Source: GLS, Volume 4, Chapter 2, Proposition 3.6(e) and Section 6.
The proof here uses the already available simplicity and two-centrality from
Theorem 1, rather than the earlier source counting argument.
-/

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII

universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Two-centrality makes the source parameter `m` odd. -/
public theorem action_m_odd
    (h : IsProductDisconnected Z M) (hs : SimpleReduction Z M)
    {z : G} (hzZ : z ∈ Z) (hzM : z ∈ M) : Odd (theorem4bM M z) := by
  obtain ⟨S, _, hSc⟩ := hs.two_central z hzZ
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hSc ⟨s, hs⟩).eq.symm
  have hSM : (S : Subgroup G) ≤ M := hSC.trans (h.centralizer_le hzZ hzM)
  let C := (M ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf M
  have hsub : ((S.subtype hSM) : Subgroup M) ≤ C := by
    intro s hs
    exact ⟨s.property, hSC hs⟩
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  intro hdvd
  exact (S.subtype hSM).not_dvd_index (hdvd.trans (Subgroup.index_dvd_of_le hsub))

/-- The source parameter exceeds one in the simple reduction. -/
public theorem action_one_lt_m
    (h : IsProductDisconnected Z M) (hs : SimpleReduction Z M)
    {z : G} (hzZ : z ∈ Z) (hzM : z ∈ M) : 1 < theorem4bM M z := by
  let C := (M ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf M
  have hCne : C ≠ ⊤ := by
    intro hC
    have hMC : M ≤ Subgroup.centralizer ({z} : Set G) :=
      (Subgroup.subgroupOf_eq_top.mp hC).trans inf_le_right
    obtain ⟨S, hzS, hSc⟩ := hs.two_central z hzZ
    have hSM : (S : Subgroup G) ≤ M := by
      intro s hsS
      exact h.centralizer_le hzZ hzM
        (Subgroup.mem_centralizer_singleton_iff.mpr (hSc ⟨s, hsS⟩).eq.symm)
    have hcore : pPrimeCore 2 G = ⊥ := by
      rcases hs.simple.eq_bot_or_eq_top_of_normal (pPrimeCore 2 G) inferInstance with hc | hc
      · exact hc
      · have hzcore : z ∈ pPrimeCore 2 G := hc ▸ Subgroup.mem_top z
        have hd := (pPrimeCore 2 G).orderOf_dvd_natCard hzcore
        rw [orderOf_eq_prime (h.involutions z hzZ).sq_eq_one (h.involutions z hzZ).ne_one] at hd
        exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp
          (pPrimeCore_coprime_card (p := 2))) hd)
    have hzc : z ∈ Subgroup.center G := by
      apply Glauberman.ZStar.glauberman_zstar_corefree hcore S z
        (h.involutions z hzZ) hzS
      · intro s hsS
        exact (hSc ⟨s, hsS⟩).eq.symm
      · refine ⟨hzS, ?_⟩
        intro g hg
        have hgM : g ∈ M := (h.conjugate_mem_iff z hzZ hzM g).mp (hSM hg)
        have hgC := Subgroup.mem_centralizer_singleton_iff.mp (hMC hgM)
        change g * z * g⁻¹ = z
        rw [hgC]
        simp
    apply h.proper
    apply top_unique
    intro g _
    apply h.centralizer_le hzZ hzM
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_center_iff.mp hzc) g)
  exact Subgroup.one_lt_index_of_ne_top hCne

/-- The nontrivial prime-share clause of (6A), with a distinguished involution. -/
public theorem action_exists_odd_prime_share
    (h : IsProductDisconnected Z M) (hs : SimpleReduction Z M) :
    ∃ z ∈ Z, z ∈ M ∧ ∃ p : ℕ,
      p.Prime ∧ Odd p ∧ 2 ≤ theorem4bPrimeShare M z p := by
  obtain ⟨z, hzZ, hzM⟩ := h.nonempty
  have hlt := action_one_lt_m h hs hzZ hzM
  have ho := action_m_odd h hs hzZ hzM
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd (by omega : theorem4bM M z ≠ 1)
  refine ⟨z, hzZ, hzM, p, hp, ho.of_dvd_nat hdvd, ?_⟩
  have hexp : 1 ≤ (theorem4bM M z).factorization p :=
    (hp.dvd_iff_one_le_factorization (by omega)).mp hdvd
  exact hp.two_le.trans (by
    simpa [theorem4bPrimeShare] using Nat.pow_le_pow_right hp.pos hexp)

end BenderSuzuki.ZD
