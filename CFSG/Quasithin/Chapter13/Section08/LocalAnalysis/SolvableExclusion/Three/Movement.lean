module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Basic
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.PCoreSurjective

/-!
# Finding the odd prime moved by Vα*

If a two-subgroup centralizes every odd prime core and the two-core is
trivial, it centralizes the Fitting subgroup. Solvable Fitting
self-centralization then puts it in the odd core, forcing it to be trivial.
Apply this in H/O₂(H), whose two-core vanishes by the core lifting theorem.

This proves the first existence step of the supercritical argument, with
the genuine star image of Vα. Selecting and lifting a small supercritical
subgroup and proving Frattini irreducibility are further obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.13, printed p.950.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three
open Subgroup
variable {G : Type*} [Group G]

/-- A nontrivial two-subgroup of a finite solvable group with trivial two-core
must move an odd prime core. -/
theorem exists_odd_core_moved [Finite G]
    (hsolv : Group.IsSolvable G) (hcore : pCore 2 G = ⊥)
    (A : Subgroup G) (hA : IsPGroup 2 A) (hne : A ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ ⁅pCore p G, A⁆ ≠ ⊥ := by
  classical
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hAF : A ≤ centralizer (fittingSubgroup G : Set G) := by
    apply le_centralizer_iff.mpr
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun q => ?_
    have hq := Nat.prime_of_mem_primeFactors q.val.property
    by_cases he : q.val.val = 2
    · rw [he, hcore]
      exact bot_le
    · exact commutator_eq_bot_iff_le_centralizer.mp
        (h q.val.val hq (hq.odd_of_ne_two he))
  have hle : A ≤ pPrimeCore 2 G :=
    (hAF.trans (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv)).trans
      (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore)
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card (pPrimeCore 2 G)) := by
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := G)).pow_left n
  have hdis : Disjoint A (pPrimeCore 2 G) := disjoint_of_coprime_natCard hcop
  exact hne (le_bot_iff.mp ((le_inf le_rfl hle).trans hdis.le_bot))


/-- Movement of an odd core in the actual quotient of a solvable H. -/
theorem exists_odd_core_moved_in_star [Finite G] {H Vα : Subgroup G}
    (hs : Group.IsSolvable H) (hVα : IsPGroup 2 Vα)
    (hne : Source.starImage H Vα ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      ⁅pCore p (Source.Hstar H), Source.starImage H Vα⁆ ≠ ⊥ := by
  let := hs
  have hcore : pCore 2 (Source.Hstar H) = ⊥ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hq := QuotientGroup.mk'_surjective (pCore 2 H)
    have hk : IsPGroup 2 q.ker := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup
    have hm := congrArg (map q) (q.comap_pCore_of_ker_isPGroup hq hk)
    rw [map_comap_eq_self_of_surjective hq] at hm
    exact hm.trans (QuotientGroup.map_mk'_self _)
  exact exists_odd_core_moved inferInstance hcore _ (starImage_isPGroup H Vα hVα) hne

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three

end
