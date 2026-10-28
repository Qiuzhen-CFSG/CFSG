module

public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.AbelianCoprimeKernel

/-!
# Nilpotence from residual centralization of prime cores

For a finite solvable group, assume that Oᵖ(G) centralizes Oₚ(G) for every
prime dividing the order of F(G). Then F(G) = G. Prime cores outside that
prime domain are trivial, so no additional centralization assumption is needed.

For each p, let Y centralize all the other prime cores. It contains every
p-subgroup. Its p-residual R centralizes F(G), and solvable Fitting
self-centralization makes R abelian. Since R is p-perfect, its order is
prime to p; its normal Sylow factors therefore lie in the other prime cores
and are central in Y. Thus Y is a central extension of a p-group, hence
normal nilpotent. Every Sylow subgroup of G consequently lies in F(G).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Lemma A.1.4, printed p.20 (PDF p.31).
-/

public section

open Subgroup

variable {G : Type*} [Group G] [Finite G]

private theorem residual_centralizes_all_prime_cores
    (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card (fittingSubgroup G) →
      pResidual p G ≤ centralizer (pCore p G : Set G))
    (p : ℕ) (hp : p.Prime) :
    pResidual p G ≤ centralizer (pCore p G : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hd : p ∣ Nat.card (fittingSubgroup G)
  · exact h p hp hd
  have hbot : pCore p G = ⊥ := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := G)).exists_card_eq
    have hn0 : n = 0 := by
      by_contra hn0
      exact hd ((dvd_pow_self p hn0).trans
        (hn ▸ card_dvd_of_le (pCore_le_fitting G p)))
    apply card_eq_one.mp
    rw [hn, hn0, pow_zero]
  rw [hbot]
  intro x _ y hy
  have hy1 : y = 1 := hy
  simp [hy1]

private theorem sylow_le_fitting_of_residual_centralizes
    (hsolv : Group.IsSolvable G)
    (h : ∀ p : ℕ, p.Prime → pResidual p G ≤ centralizer (pCore p G : Set G))
    (p : ℕ) [Fact p.Prime] (S : Sylow p G) :
    (S : Subgroup G) ≤ fittingSubgroup G := by
  -- The other prime cores are centralized by every p-subgroup.
  let Y : Subgroup G := ⨅ q : {q : ℕ // q.Prime ∧ q ≠ p},
    centralizer (pCore q.val G : Set G)
  have hYq (q : ℕ) (hq : q.Prime) (hne : q ≠ p) :
      Y ≤ centralizer (pCore q G : Set G) :=
    iInf_le (fun r : {r : ℕ // r.Prime ∧ r ≠ p} =>
      centralizer (pCore r.val G : Set G)) ⟨q, hq, hne⟩
  have hSY : (S : Subgroup G) ≤ Y := by
    change (S : Subgroup G) ≤ ⨅ q : {q : ℕ // q.Prime ∧ q ≠ p},
      centralizer (pCore q.val G : Set G)
    refine le_iInf fun q => ?_
    apply le_trans ?_ (h q.val q.property.1)
    intro x hx
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_orderOf_eq_pow ⟨x, hx⟩
    apply mem_pResidual_of_orderOf_coprime
    have hxord : orderOf x = p ^ n :=
      (Subgroup.orderOf_coe (⟨x, hx⟩ : (S : Subgroup G))).trans hn
    rw [hxord]
    exact ((Nat.coprime_primes q.property.1 (Fact.out : p.Prime)).mpr
      q.property.2).pow_right n
  let : Y.Normal := normal_iInf_normal fun q => inferInstance
  let R : Subgroup G := (pResidual p Y).map Y.subtype
  have hRY : R ≤ Y := map_subtype_le _
  -- The residual of Y centralizes every prime core, hence lies in Z(F(G)).
  have hRC : R ≤ centralizer (fittingSubgroup G : Set G) := by
    apply subgroup_le_centralizer_fitting_of_le_centralizer_pCores
    intro q
    by_cases heq : q.val.val = p
    · rw [heq]
      exact (map_pResidual_le p Y.subtype).trans (h p Fact.out)
    · exact hRY.trans (hYq q.val.val (Nat.prime_of_mem_primeFactors q.val.property) heq)
  have hRF : R ≤ fittingSubgroup G := hRC.trans
    (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv)
  let : CommGroup R := { (inferInstance : Group R) with
    mul_comm := fun a b => Subtype.ext ((hRC a.property) b.val (hRF b.property)).symm }
  have hRcop : Nat.Coprime p (Nat.card R) := by
    have ht : pResidual p R = ⊤ :=
      (pResidual_eq_top_iff p R).mpr (isPPerfect_embedded_pResidual p Y)
    have hc := coprime_card_pResidual_of_commGroup (A := R) p
    simpa only [ht, card_top] using hc
  -- Its Sylow factors belong to the other prime cores, so it is central in Y.
  have hcentral : R ≤ centralizer (Y : Set G) := by
    rw [← Sylow.iSup_sylow_map_eq_top (N := R)]
    simp only [map_iSup]
    refine iSup₂_le fun q hq => ?_
    let : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
    have hne : q ≠ p := by
      intro heq
      exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hRcop
        (heq ▸ Nat.dvd_of_mem_primeFactors hq)
    exact (Sylow.map_le_pCore (inferInstance : R.Normal)
      (inferInstance : Group.IsNilpotent R) q (default : Sylow q R)).trans
      (le_centralizer_iff.mp (hYq q Fact.out hne))
  have hnilY : Group.IsNilpotent Y := by
    let : Group.IsNilpotent (Y ⧸ pResidual p Y) :=
      (isPGroup_quotient_pResidual p).isNilpotent
    apply Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (pResidual p Y))
    intro x hx
    have hxR : x.val ∈ R := mem_map_of_mem Y.subtype
      ((QuotientGroup.eq_one_iff x).mp hx)
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext ((hcentral hxR) y.val y.property)
  exact hSY.trans (le_sSup ⟨inferInstance, hnilY⟩)

/-- A finite solvable group is its Fitting subgroup if each prime residual
centralizes the corresponding prime core, for primes dividing the Fitting order. -/
theorem fitting_eq_top_of_pResidual_le_centralizer_pCore
    (hsolv : Group.IsSolvable G)
    (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card (fittingSubgroup G) →
      pResidual p G ≤ centralizer (pCore p G : Set G)) :
    fittingSubgroup G = ⊤ := by
  apply top_unique
  rw [← Sylow.iSup_sylow_eq_top (G := G)]
  refine iSup₂_le fun p hp => ?_
  let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  exact sylow_le_fitting_of_residual_centralizes hsolv
    (residual_centralizes_all_prime_cores h) p default
