module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_12_4
public import Theory.AlgebraicGroup.Cartan.Kernels
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
The type `D` universal-center calculation in GLS3, Theorem 1.12.5(c)-(d).

The center-character reduction identifies a universal center with the
multiplicative kernel of the numbered Cartan relations.  This module records
the type-specific part of that calculation without importing the unresolved
center theorem: the type `D_m` relation kernel has two independent
second-root parameters when `m` is even and one fourth-root parameter when
`m` is odd.  The final center statement is exposed through an explicit
character/coroot-kernel equivalence, so the geometric center-to-kernel bridge
can be supplied by the lower-level center-character module.
-/

universe u

open scoped BigOperators

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

public noncomputable def typeDCartanKernel (m : ℕ) :
    Subgroup (Fin m → kˣ) where
  carrier := {t | ∀ j,
    (∏ i, t i ^ dynkinCartanEntry ⟨.D, m⟩ i j) = 1}
  one_mem' := by
    intro j
    simp
  mul_mem' := by
    intro a b ha hb j
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    simp_rw [Pi.mul_apply, mul_zpow]
    rw [Finset.prod_mul_distrib]
    rw [ha, hb, one_mul]
  inv_mem' := by
    intro a ha j
    simp only [Set.mem_ofPred_eq] at ha ⊢
    simp_rw [Pi.inv_apply, inv_zpow]
    rw [Finset.prod_inv_distrib]
    rw [ha, inv_one]

private lemma typeDCartanKernel_relation
    (m : ℕ) (t : Fin m → kˣ) (ht : t ∈ typeDCartanKernel (k := k) m) :
    ∀ j, (∏ i, t i ^ dynkinCartanEntry ⟨.D, m⟩ i j) = 1 := by
  exact ht

private lemma typeD_rank_internal (m : ℕ) (hm : 4 ≤ m) :
    1 ≤ m - 3 := by omega

private lemma typeD_prod_eq_support
    {m : ℕ} (f : Fin m → kˣ) (S : Finset (Fin m))
    (hf : ∀ x, x ∉ S → f x = 1) :
    (∏ x, f x) = ∏ x ∈ S, f x := by
  symm
  apply Finset.prod_subset (by simp)
  intro x _ hx
  exact hf x hx

private lemma typeDCartanKernel_mem_of_coordinates
    (m : ℕ) (hm : 4 ≤ m) (t : Fin m → kˣ) (ω : kˣ)
    (hω : ω ^ 2 = 1)
    (hchain : ∀ i : Fin (m - 2),
      t ⟨i.val, by omega⟩ = ω ^ (i.val + 1))
    (hforksq : t ⟨m - 2, by omega⟩ ^ 2 = ω ^ (m - 2))
    (hfork : t ⟨m - 1, by omega⟩ =
      ω * t ⟨m - 2, by omega⟩) :
    t ∈ typeDCartanKernel (k := k) m := by
  intro j
  let term : Fin m → kˣ := fun i =>
    t i ^ dynkinCartanEntry ⟨.D, m⟩ i j
  by_cases hj0 : j.val = 0
  · let s : Fin m := ⟨1, by omega⟩
    have hsupp : (∏ i, term i) = ∏ i ∈ ({j, s} : Finset (Fin m)), term i := by
      apply typeD_prod_eq_support
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      have hxj : x ≠ j := hx.1
      have hxs : x ≠ s := hx.2
      have hx0 : x.val ≠ 0 := by
        intro h
        apply hxj
        apply Fin.ext
        omega
      have hx1 : x.val ≠ 1 := by
        intro h
        apply hxs
        apply Fin.ext
        simpa [s] using h
      have hadj : ¬(
          (x.val + 1 = j.val ∧ j.val + 2 < m) ∨
          (j.val + 1 = x.val ∧ x.val + 2 < m) ∨
          (x.val + 3 = m ∧ (j.val + 2 = m ∨ j.val + 1 = m)) ∨
          (j.val + 3 = m ∧ (x.val + 2 = m ∨ x.val + 1 = m))) := by
        omega
      simp only [term]
      rw [dynkinCartanEntry, if_neg hxj, if_neg hadj]
      simp
    have hjs : j ≠ s := by
      intro h
      have := congrArg Fin.val h
      simp [s, hj0] at this
    rw [hsupp, Finset.prod_pair hjs]
    simp only [term]
    have hdiag : dynkinCartanEntry ⟨.D, m⟩ j j = 2 := by
      simp [dynkinCartanEntry]
    have hedge : dynkinCartanEntry ⟨.D, m⟩ s j = -1 := by
      simp [dynkinCartanEntry, s]
      omega
    rw [hdiag, hedge]
    simp only [zpow_ofNat, zpow_neg_one]
    have h0 := hchain ⟨0, by omega⟩
    have h1 := hchain ⟨1, by omega⟩
    simp only [Nat.reduceAdd, pow_one] at h0 h1
    have htj : t j = ω := by
      calc
        t j = t ⟨0, by omega⟩ := by congr 1; exact Fin.ext hj0
        _ = ω := h0
    have hts : t s = ω ^ 2 := by simpa [s] using h1
    rw [htj, hts, hω]
    simp
  · by_cases hjchain : j.val < m - 3
    · let p : Fin m := ⟨j.val - 1, by omega⟩
      let s : Fin m := ⟨j.val + 1, by omega⟩
      have hsupp :
          (∏ i, term i) = ∏ i ∈ ({p, j, s} : Finset (Fin m)), term i := by
        apply typeD_prod_eq_support
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        have hxp : x.val ≠ j.val - 1 := by
          intro h
          apply hx.1
          apply Fin.ext
          simpa [p] using h
        have hxj : x ≠ j := hx.2.1
        have hxjval : x.val ≠ j.val := by
          intro h
          apply hxj
          exact Fin.ext h
        have hxs : x.val ≠ j.val + 1 := by
          intro h
          apply hx.2.2
          apply Fin.ext
          simpa [s] using h
        have hadj : ¬(
            (x.val + 1 = j.val ∧ j.val + 2 < m) ∨
            (j.val + 1 = x.val ∧ x.val + 2 < m) ∨
            (x.val + 3 = m ∧ (j.val + 2 = m ∨ j.val + 1 = m)) ∨
            (j.val + 3 = m ∧ (x.val + 2 = m ∨ x.val + 1 = m))) := by
          omega
        simp only [term]
        rw [dynkinCartanEntry, if_neg hxj, if_neg hadj]
        simp
      have hpj : p ≠ j := by
        intro h
        have := congrArg Fin.val h
        simp [p] at this
        omega
      have hps : p ≠ s := by
        intro h
        have := congrArg Fin.val h
        simp [p, s] at this
      have hjs : j ≠ s := by
        intro h
        have := congrArg Fin.val h
        simp [s] at this
      rw [hsupp, Finset.prod_insert (by simp [hpj, hps]),
        Finset.prod_pair hjs]
      simp only [term]
      have hp : t p = ω ^ j.val := by
        simpa [p, show j.val - 1 + 1 = j.val by omega] using
          hchain ⟨j.val - 1, by omega⟩
      have hj : t j = ω ^ (j.val + 1) := by
        simpa using hchain ⟨j.val, by omega⟩
      have hs : t s = ω ^ (j.val + 2) := by
        simpa [s] using hchain ⟨j.val + 1, by omega⟩
      have hep : dynkinCartanEntry ⟨.D, m⟩ p j = -1 := by
        simp [dynkinCartanEntry, p]
        omega
      have hej : dynkinCartanEntry ⟨.D, m⟩ j j = 2 := by
        simp [dynkinCartanEntry]
      have hes : dynkinCartanEntry ⟨.D, m⟩ s j = -1 := by
        simp [dynkinCartanEntry, s]
        omega
      rw [hep, hej, hes]
      simp only [zpow_neg_one, zpow_ofNat]
      rw [hp, hj, hs]
      group
    · have hjge : m - 3 ≤ j.val := by omega
      have hjlt : j.val < m := j.isLt
      have hjcases : j.val = m - 3 ∨ j.val = m - 2 ∨ j.val = m - 1 := by
        omega
      rcases hjcases with hjbranch | hjrest
      · let p : Fin m := ⟨m - 4, by omega⟩
        let u : Fin m := ⟨m - 2, by omega⟩
        let v : Fin m := ⟨m - 1, by omega⟩
        have hsupp :
            (∏ i, term i) =
              ∏ i ∈ ({p, j, u, v} : Finset (Fin m)), term i := by
          apply typeD_prod_eq_support
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
          have hxp : x.val ≠ m - 4 := by
            intro h
            apply hx.1
            apply Fin.ext
            simpa [p] using h
          have hxj : x ≠ j := hx.2.1
          have hxjval : x.val ≠ j.val := by
            intro h
            apply hxj
            exact Fin.ext h
          have hxu : x.val ≠ m - 2 := by
            intro h
            apply hx.2.2.1
            apply Fin.ext
            simpa [u] using h
          have hxv : x.val ≠ m - 1 := by
            intro h
            apply hx.2.2.2
            apply Fin.ext
            simpa [v] using h
          have hadj : ¬(
              (x.val + 1 = j.val ∧ j.val + 2 < m) ∨
              (j.val + 1 = x.val ∧ x.val + 2 < m) ∨
              (x.val + 3 = m ∧ (j.val + 2 = m ∨ j.val + 1 = m)) ∨
              (j.val + 3 = m ∧ (x.val + 2 = m ∨ x.val + 1 = m))) := by
            omega
          simp only [term]
          rw [dynkinCartanEntry, if_neg hxj, if_neg hadj]
          simp
        have hpj : p ≠ j := by intro h; have := congrArg Fin.val h; simp [p, hjbranch] at this; omega
        have hpu : p ≠ u := by intro h; have := congrArg Fin.val h; simp [p, u] at this; omega
        have hpv : p ≠ v := by intro h; have := congrArg Fin.val h; simp [p, v] at this; omega
        have hju : j ≠ u := by intro h; have := congrArg Fin.val h; simp [hjbranch, u] at this; omega
        have hjv : j ≠ v := by intro h; have := congrArg Fin.val h; simp [hjbranch, v] at this; omega
        have huv : u ≠ v := by intro h; have := congrArg Fin.val h; simp [u, v] at this; omega
        rw [hsupp, Finset.prod_insert (by simp [hpj, hpu, hpv]),
          Finset.prod_insert (by simp [hju, hjv]), Finset.prod_pair huv]
        simp only [term]
        have hp : t p = ω ^ (m - 3) := by
          simpa [p, show m - 4 + 1 = m - 3 by omega] using
            hchain ⟨m - 4, by omega⟩
        have hj : t j = ω ^ (m - 2) := by
          calc
            t j = t ⟨m - 3, by omega⟩ := by
              congr 1
              exact Fin.ext hjbranch
            _ = ω ^ (m - 2) := by
              simpa [show m - 3 + 1 = m - 2 by omega] using
                hchain ⟨m - 3, by omega⟩
        have hep : dynkinCartanEntry ⟨.D, m⟩ p j = -1 := by
          simp [dynkinCartanEntry, p, hjbranch]
          omega
        have hej : dynkinCartanEntry ⟨.D, m⟩ j j = 2 := by
          simp [dynkinCartanEntry]
        have heu : dynkinCartanEntry ⟨.D, m⟩ u j = -1 := by
          simp [dynkinCartanEntry, u, hjbranch]
          omega
        have hev : dynkinCartanEntry ⟨.D, m⟩ v j = -1 := by
          simp [dynkinCartanEntry, v, hjbranch]
          omega
        rw [hep, hej, heu, hev]
        simp only [zpow_neg_one, zpow_ofNat]
        have htu : t u = t ⟨m - 2, by omega⟩ := by rfl
        rw [hp, hj, hfork, htu]
        have hstep : ω ^ (m - 2) = ω ^ (m - 3) * ω := by
          rw [show m - 2 = (m - 3) + 1 by omega, pow_succ]
        calc
          (ω ^ (m - 3))⁻¹ *
                ((ω ^ (m - 2)) ^ 2 *
                  ((t ⟨m - 2, by omega⟩)⁻¹ *
                    (ω * t ⟨m - 2, by omega⟩)⁻¹)) =
              (ω ^ (m - 3))⁻¹ * (ω ^ (m - 2)) ^ 2 *
                (ω * t ⟨m - 2, by omega⟩ ^ 2)⁻¹ := by group
          _ = (ω ^ (m - 3))⁻¹ * (ω ^ (m - 2)) ^ 2 *
                (ω * ω ^ (m - 2))⁻¹ := by rw [hforksq]
          _ = (ω ^ (m - 3))⁻¹ * ω ^ (m - 2) * ω⁻¹ := by group
          _ = 1 := by rw [hstep]; group
      · rcases hjrest with hjfork | hjfork
        · let p : Fin m := ⟨m - 3, by omega⟩
          have hsupp :
              (∏ i, term i) = ∏ i ∈ ({p, j} : Finset (Fin m)), term i := by
            apply typeD_prod_eq_support
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
            have hxp : x.val ≠ m - 3 := by
              intro h
              apply hx.1
              apply Fin.ext
              simpa [p] using h
            have hxj : x ≠ j := hx.2
            have hxjval : x.val ≠ j.val := by
              intro h
              apply hxj
              exact Fin.ext h
            have hadj : ¬(
                (x.val + 1 = j.val ∧ j.val + 2 < m) ∨
                (j.val + 1 = x.val ∧ x.val + 2 < m) ∨
                (x.val + 3 = m ∧ (j.val + 2 = m ∨ j.val + 1 = m)) ∨
                (j.val + 3 = m ∧ (x.val + 2 = m ∨ x.val + 1 = m))) := by
              omega
            simp only [term]
            rw [dynkinCartanEntry, if_neg hxj, if_neg hadj]
            simp
          have hpj : p ≠ j := by intro h; have := congrArg Fin.val h; simp [p, hjfork] at this; omega
          rw [hsupp, Finset.prod_pair hpj]
          simp only [term]
          have hp : t p = ω ^ (m - 2) := by
            simpa [p, show m - 3 + 1 = m - 2 by omega] using
              hchain ⟨m - 3, by omega⟩
          have hj : t j ^ 2 = ω ^ (m - 2) := by
            calc
              t j ^ 2 = t ⟨m - 2, by omega⟩ ^ 2 := by
                congr 2
                exact Fin.ext hjfork
              _ = ω ^ (m - 2) := hforksq
          have hep : dynkinCartanEntry ⟨.D, m⟩ p j = -1 := by
            simp [dynkinCartanEntry, p, hjfork]
            omega
          have hej : dynkinCartanEntry ⟨.D, m⟩ j j = 2 := by
            simp [dynkinCartanEntry]
          rw [hep, hej]
          simp only [zpow_neg_one, zpow_ofNat]
          rw [hp, hj]
          simp
        · let p : Fin m := ⟨m - 3, by omega⟩
          have hsupp :
              (∏ i, term i) = ∏ i ∈ ({p, j} : Finset (Fin m)), term i := by
            apply typeD_prod_eq_support
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
            have hxp : x.val ≠ m - 3 := by
              intro h
              apply hx.1
              apply Fin.ext
              simpa [p] using h
            have hxj : x ≠ j := hx.2
            have hxjval : x.val ≠ j.val := by
              intro h
              apply hxj
              exact Fin.ext h
            have hadj : ¬(
                (x.val + 1 = j.val ∧ j.val + 2 < m) ∨
                (j.val + 1 = x.val ∧ x.val + 2 < m) ∨
                (x.val + 3 = m ∧ (j.val + 2 = m ∨ j.val + 1 = m)) ∨
                (j.val + 3 = m ∧ (x.val + 2 = m ∨ x.val + 1 = m))) := by
              omega
            simp only [term]
            rw [dynkinCartanEntry, if_neg hxj, if_neg hadj]
            simp
          have hpj : p ≠ j := by intro h; have := congrArg Fin.val h; simp [p, hjfork] at this; omega
          rw [hsupp, Finset.prod_pair hpj]
          simp only [term]
          have hp : t p = ω ^ (m - 2) := by
            simpa [p, show m - 3 + 1 = m - 2 by omega] using
              hchain ⟨m - 3, by omega⟩
          have hj : t j = ω * t ⟨m - 2, by omega⟩ := by
            calc
              t j = t ⟨m - 1, by omega⟩ := by
                congr 1
                exact Fin.ext hjfork
              _ = ω * t ⟨m - 2, by omega⟩ := hfork
          have hep : dynkinCartanEntry ⟨.D, m⟩ p j = -1 := by
            simp [dynkinCartanEntry, p, hjfork]
            omega
          have hej : dynkinCartanEntry ⟨.D, m⟩ j j = 2 := by
            simp [dynkinCartanEntry]
          rw [hep, hej]
          simp only [zpow_neg_one, zpow_ofNat]
          rw [hp, hj, mul_pow, hω, hforksq]
          simp

/-! The raw Cartan-kernel coordinates, before choosing a concrete center
isomorphism.  The displayed coordinate equations are exactly the fork
calculation in GLS3: the chain is generated by `omega`, the two fork entries
are related by `v = omega * u`, and parity determines the remaining order.
-/
public theorem typeD_cartan_kernel_coordinates
    (m : ℕ) (hm : 4 ≤ m) (t : Fin m → kˣ)
    (ht : t ∈ typeDCartanKernel (k := k) m) :
    ∃ ω : kˣ, ω ^ 2 = 1 ∧
      (∀ i : Fin (m - 2),
        t ⟨i.val, by omega⟩ = ω ^ (i.val + 1)) ∧
      t ⟨m - 2, by omega⟩ ^ 2 = ω ^ (m - 2) ∧
      t ⟨m - 1, by omega⟩ = ω * t ⟨m - 2, by omega⟩ := by
  have hmEq : m - 3 + 3 = m := by omega
  have hmEq1 : m - 3 + 1 = m - 2 := by omega
  have hmEq2 : m - 3 + 2 = m - 1 := by omega
  let e : Fin (m - 3 + 3) ≃ Fin m := Fin.castOrderIso hmEq
  let t' : Fin (m - 3 + 3) → kˣ := fun i => t (e i)
  have hrel : ∀ j' : Fin (m - 3 + 3),
      (∏ i, t' i ^ dynkinCartanEntry ⟨.D, m - 3 + 3⟩ i j') = 1 := by
    intro j'
    have hentry (i : Fin (m - 3 + 3)) :
        dynkinCartanEntry ⟨.D, m - 3 + 3⟩ i j' =
          dynkinCartanEntry ⟨.D, m⟩ (e i) (e j') := by
      simp [e, Fin.castOrderIso, dynkinCartanEntry, hmEq]
      rfl
    have hprod := Fintype.prod_equiv e
      (fun i => t' i ^ dynkinCartanEntry ⟨.D, m - 3 + 3⟩ i j')
      (fun i => t i ^ dynkinCartanEntry ⟨.D, m⟩ i (e j')) (by
        intro i
        simp [t', hentry])
    rw [hprod]
    simpa [e] using typeDCartanKernel_relation m t ht (e j')
  have hraw := dynkinCartanRelationKernel_D (k := k) (m - 3)
    (typeD_rank_internal m hm)
    t' hrel
  rcases hraw with ⟨ω, hω, hchain, hforksq, hfork⟩
  refine ⟨ω, hω, ?_, ?_, ?_⟩
  · intro i
    simpa [t', e, hmEq1] using hchain (Fin.cast hmEq1.symm i)
  · simpa [t', e, hmEq1] using hforksq
  · simpa [t', e, hmEq1, hmEq2] using hfork

public theorem typeD_cartan_kernel_even_coordinates
    (m : ℕ) (hm : 4 ≤ m) (heven : m % 2 = 0)
    (t : Fin m → kˣ)
    (ht : t ∈ typeDCartanKernel (k := k) m) :
    ∃ ω η : kˣ, ω ^ 2 = 1 ∧ η ^ 2 = 1 ∧
      (∀ i : Fin (m - 2),
        t ⟨i.val, by omega⟩ = ω ^ (i.val + 1)) ∧
      t ⟨m - 2, by omega⟩ = η ∧
      t ⟨m - 1, by omega⟩ = ω * η := by
  obtain ⟨ω, hω, hchain, hforksq, hfork⟩ :=
    typeD_cartan_kernel_coordinates m hm t ht
  let η := t ⟨m - 2, by omega⟩
  have hη : η ^ 2 = 1 := by
    rw [show η = t ⟨m - 2, by omega⟩ by rfl, hforksq]
    have hpow : ω ^ (m - 2) = 1 := by
      have hdiv : m % 2 + 2 * (m / 2) = m := Nat.mod_add_div m 2
      have hm2even : Even (m - 2) := by
        refine ⟨m / 2 - 1, ?_⟩
        omega
      obtain ⟨q, hq⟩ := hm2even
      rw [hq, show q + q = 2 * q by omega, pow_mul, hω]
      simp
    exact hpow
  refine ⟨ω, η, hω, hη, hchain, rfl, ?_⟩
  simpa [η] using hfork

public theorem typeD_cartan_kernel_odd_coordinates
    (m : ℕ) (hm : 4 ≤ m) (hodd : m % 2 = 1)
    (t : Fin m → kˣ)
    (ht : t ∈ typeDCartanKernel (k := k) m) :
    ∃ η : kˣ, η ^ 4 = 1 ∧
      (∀ i : Fin (m - 2),
        t ⟨i.val, by omega⟩ = (η ^ 2) ^ (i.val + 1)) ∧
      t ⟨m - 2, by omega⟩ = η ∧
      t ⟨m - 1, by omega⟩ = η ^ 3 := by
  obtain ⟨ω, hω, hchain, hforksq, hfork⟩ :=
    typeD_cartan_kernel_coordinates m hm t ht
  let η := t ⟨m - 2, by omega⟩
  have hηsq : η ^ 2 = ω := by
    rw [show η = t ⟨m - 2, by omega⟩ by rfl, hforksq]
    have hpow : ω ^ (m - 2) = ω := by
      have hdiv : m % 2 + 2 * (m / 2) = m := Nat.mod_add_div m 2
      have hmForm : m - 2 = 2 * (m / 2 - 1) + 1 := by omega
      rw [hmForm, pow_add, pow_mul, hω]
      simp
    exact hpow
  have hη4 : η ^ 4 = 1 := by
    calc
      η ^ 4 = (η ^ 2) ^ 2 := by group
      _ = ω ^ 2 := by rw [hηsq]
      _ = 1 := hω
  refine ⟨η, hη4, ?_, rfl, ?_⟩
  · intro i
    rw [hchain i, hηsq]
  · calc
      t ⟨m - 1, by omega⟩ = ω * t ⟨m - 2, by omega⟩ := hfork
      _ = ω * η := by rfl
      _ = η ^ 3 := by rw [← hηsq]; simp [pow_succ, mul_assoc]

private def evenParameterValue (m : ℕ)
    (p : rootsOfUnity 2 k × rootsOfUnity 2 k) (i : Fin m) : kˣ :=
  if i.val < m - 2 then (p.1 : kˣ) ^ (i.val + 1)
  else if i.val = m - 2 then (p.2 : kˣ)
  else (p.1 : kˣ) * p.2

private noncomputable def evenParameterMap
    (m : ℕ) (hm : 4 ≤ m) (heven : m % 2 = 0) :
    (rootsOfUnity 2 k × rootsOfUnity 2 k) →*
      typeDCartanKernel (k := k) m := by
  let f : (rootsOfUnity 2 k × rootsOfUnity 2 k) →* (Fin m → kˣ) :=
    { toFun := evenParameterValue m
      map_one' := by
        funext i
        simp [evenParameterValue]
      map_mul' := by
        intro a b
        funext i
        by_cases hlt : i.val < m - 2
        · simp [evenParameterValue, hlt, mul_pow]
        · by_cases heq : i.val = m - 2
          · simp [evenParameterValue, heq]
          · simp [evenParameterValue, hlt, heq]
            ac_rfl }
  exact f.codRestrict (typeDCartanKernel (k := k) m) (by
    intro p
    have hω : (p.1 : kˣ) ^ 2 = 1 := by
      exact (mem_rootsOfUnity 2 (p.1 : kˣ)).mp p.1.2
    have hη : (p.2 : kˣ) ^ 2 = 1 := by
      exact (mem_rootsOfUnity 2 (p.2 : kˣ)).mp p.2.2
    apply typeDCartanKernel_mem_of_coordinates m hm _ (p.1 : kˣ) hω
    · intro i
      simp [f, evenParameterValue, i.isLt]
    · have hdiv : m % 2 + 2 * (m / 2) = m := Nat.mod_add_div m 2
      have hm2even : Even (m - 2) := by
        refine ⟨m / 2 - 1, ?_⟩
        omega
      obtain ⟨q, hq⟩ := hm2even
      simp [f, evenParameterValue, hq,
        show q + q = 2 * q by omega, pow_mul, hω, hη]
    · change evenParameterValue m p ⟨m - 1, by omega⟩ =
        (p.1 : kˣ) * evenParameterValue m p ⟨m - 2, by omega⟩
      have hlastLt : ¬m - 1 < m - 2 := by omega
      have hlastEq : ¬m - 1 = m - 2 := by omega
      simp [evenParameterValue, hlastLt, hlastEq])

@[simp] private lemma evenParameterMap_apply
    (m : ℕ) (hm : 4 ≤ m) (heven : m % 2 = 0)
    (p : rootsOfUnity 2 k × rootsOfUnity 2 k) (i : Fin m) :
    (evenParameterMap (k := k) m hm heven p).1 i = evenParameterValue m p i := by
  rfl

private lemma evenParameterMap_injective
    (m : ℕ) (hm : 4 ≤ m) (heven : m % 2 = 0) :
    Function.Injective (evenParameterMap (k := k) m hm heven) := by
  intro a b hab
  apply Prod.ext
  · apply Subtype.ext
    have h0 := congrArg (fun t => t.1 ⟨0, by omega⟩) hab
    rw [evenParameterMap_apply, evenParameterMap_apply] at h0
    have hzero : 0 < m - 2 := by omega
    simpa [evenParameterValue, hzero] using h0
  · apply Subtype.ext
    have hlast := congrArg (fun t => t.1 ⟨m - 2, by omega⟩) hab
    rw [evenParameterMap_apply, evenParameterMap_apply] at hlast
    simpa [evenParameterValue] using hlast

private lemma evenParameterMap_surjective
    (m : ℕ) (hm : 4 ≤ m) (heven : m % 2 = 0)
    (hcoordinates : ∀ (t : Fin m → kˣ),
      t ∈ typeDCartanKernel (k := k) m →
      ∃ ω η : kˣ, ω ^ 2 = 1 ∧ η ^ 2 = 1 ∧
        (∀ i : Fin (m - 2),
          t ⟨i.val, by omega⟩ = ω ^ (i.val + 1)) ∧
        t ⟨m - 2, by omega⟩ = η ∧
        t ⟨m - 1, by omega⟩ = ω * η) :
    Function.Surjective (evenParameterMap (k := k) m hm heven) := by
  intro t
  obtain ⟨ω, η, hω, hη, hchain, hfork, hlast⟩ :=
    hcoordinates t.1 t.2
  let ω' : rootsOfUnity 2 k :=
    ⟨ω, (mem_rootsOfUnity 2 ω).mpr hω⟩
  let η' : rootsOfUnity 2 k :=
    ⟨η, (mem_rootsOfUnity 2 η).mpr hη⟩
  refine ⟨(ω', η'), ?_⟩
  apply Subtype.ext
  funext i
  rw [evenParameterMap_apply]
  by_cases hi : i.val < m - 2
  · simpa [evenParameterValue, hi, ω'] using
      (hchain ⟨i.val, hi⟩).symm
  · by_cases hifork : i.val = m - 2
    · calc
        evenParameterValue m (ω', η') i = η := by
          simp [evenParameterValue, hifork, η']
        _ = t.1 ⟨m - 2, by omega⟩ := hfork.symm
        _ = t.1 i := congrArg t.1 (Fin.ext hifork).symm
    · have hilast : i.val = m - 1 := by omega
      calc
        evenParameterValue m (ω', η') i = ω * η := by
          simp [evenParameterValue, hi, hifork, ω', η']
        _ = t.1 ⟨m - 1, by omega⟩ := hlast.symm
        _ = t.1 i := congrArg t.1 (Fin.ext hilast).symm

private def oddParameterValue (m : ℕ) (η : rootsOfUnity 4 k)
    (i : Fin m) : kˣ :=
  if i.val < m - 2 then ((η : kˣ) ^ 2) ^ (i.val + 1)
  else if i.val = m - 2 then (η : kˣ)
  else (η : kˣ) ^ 3

private noncomputable def oddParameterMap
    (m : ℕ) (hm : 4 ≤ m) (hodd : m % 2 = 1) :
    rootsOfUnity 4 k →* typeDCartanKernel (k := k) m := by
  let f : rootsOfUnity 4 k →* (Fin m → kˣ) :=
    { toFun := oddParameterValue m
      map_one' := by
        funext i
        simp [oddParameterValue]
      map_mul' := by
        intro a b
        funext i
        by_cases hlt : i.val < m - 2
        · simp [oddParameterValue, hlt, mul_pow]
        · by_cases heq : i.val = m - 2
          · simp [oddParameterValue, heq]
          · simp [oddParameterValue, hlt, heq, mul_pow] }
  exact f.codRestrict (typeDCartanKernel (k := k) m) (by
    intro η
    have hη4 : (η : kˣ) ^ 4 = 1 :=
      (mem_rootsOfUnity 4 (η : kˣ)).mp η.2
    have hω : ((η : kˣ) ^ 2) ^ 2 = 1 := by
      calc
        ((η : kˣ) ^ 2) ^ 2 = (η : kˣ) ^ 4 := by group
        _ = 1 := hη4
    apply typeDCartanKernel_mem_of_coordinates m hm _ ((η : kˣ) ^ 2) hω
    · intro i
      simp [f, oddParameterValue, i.isLt]
    · simp only [f, MonoidHom.coe_mk, OneHom.coe_mk]
      have hforkValue :
          oddParameterValue m η ⟨m - 2, by omega⟩ = (η : kˣ) := by
        simp [oddParameterValue]
      rw [hforkValue]
      have hdiv : m % 2 + 2 * (m / 2) = m := Nat.mod_add_div m 2
      have hmForm : m - 2 = 2 * (m / 2 - 1) + 1 := by omega
      symm
      rw [hmForm, pow_add, pow_mul, hω]
      simp
    · change oddParameterValue m η ⟨m - 1, by omega⟩ =
        (η : kˣ) ^ 2 * oddParameterValue m η ⟨m - 2, by omega⟩
      have hlastLt : ¬m - 1 < m - 2 := by omega
      have hlastEq : ¬m - 1 = m - 2 := by omega
      simp [oddParameterValue, hlastLt, hlastEq, pow_succ])

@[simp] private lemma oddParameterMap_apply
    (m : ℕ) (hm : 4 ≤ m) (hodd : m % 2 = 1)
    (η : rootsOfUnity 4 k) (i : Fin m) :
    (oddParameterMap (k := k) m hm hodd η).1 i = oddParameterValue m η i := by
  rfl

private lemma oddParameterMap_injective
    (m : ℕ) (hm : 4 ≤ m) (hodd : m % 2 = 1) :
    Function.Injective (oddParameterMap (k := k) m hm hodd) := by
  intro η ζ h
  apply Subtype.ext
  have hfork := congrArg (fun t => t.1 ⟨m - 2, by omega⟩) h
  rw [oddParameterMap_apply, oddParameterMap_apply] at hfork
  simpa [oddParameterValue] using hfork

private lemma oddParameterMap_surjective
    (m : ℕ) (hm : 4 ≤ m) (hodd : m % 2 = 1)
    (hcoordinates : ∀ (t : Fin m → kˣ),
      t ∈ typeDCartanKernel (k := k) m →
      ∃ η : kˣ, η ^ 4 = 1 ∧
        (∀ i : Fin (m - 2),
          t ⟨i.val, by omega⟩ = (η ^ 2) ^ (i.val + 1)) ∧
        t ⟨m - 2, by omega⟩ = η ∧
        t ⟨m - 1, by omega⟩ = η ^ 3) :
    Function.Surjective (oddParameterMap (k := k) m hm hodd) := by
  intro t
  obtain ⟨η, hη, hchain, hfork, hlast⟩ := hcoordinates t.1 t.2
  let η' : rootsOfUnity 4 k :=
    ⟨η, (mem_rootsOfUnity 4 η).mpr hη⟩
  refine ⟨η', ?_⟩
  apply Subtype.ext
  funext i
  rw [oddParameterMap_apply]
  by_cases hi : i.val < m - 2
  · simpa [oddParameterValue, hi, η'] using
      (hchain ⟨i.val, hi⟩).symm
  · by_cases hifork : i.val = m - 2
    · calc
        oddParameterValue m η' i = η := by
          simp [oddParameterValue, hifork, η']
        _ = t.1 ⟨m - 2, by omega⟩ := hfork.symm
        _ = t.1 i := congrArg t.1 (Fin.ext hifork).symm
    · have hilast : i.val = m - 1 := by omega
      calc
        oddParameterValue m η' i = η ^ 3 := by
          simp [oddParameterValue, hi, hifork, η']
        _ = t.1 ⟨m - 1, by omega⟩ := hlast.symm
        _ = t.1 i := congrArg t.1 (Fin.ext hilast).symm

/-- For even `m`, the type-`D_m` Cartan kernel has the two independent
second-root parameters at the chain origin and one fork endpoint. -/
public noncomputable def typeDEvenCartanKernelEquiv
    (m : ℕ) (hm : 4 ≤ m) (heven : m % 2 = 0) :
    (rootsOfUnity 2 k × rootsOfUnity 2 k) ≃*
      typeDCartanKernel (k := k) m :=
  MulEquiv.ofBijective (evenParameterMap (k := k) m hm heven)
    ⟨evenParameterMap_injective (k := k) m hm heven,
      evenParameterMap_surjective (k := k) m hm heven
        (typeD_cartan_kernel_even_coordinates (k := k) m hm heven)⟩

/-- For odd `m`, the type-`D_m` Cartan kernel is parametrized by the fourth
roots of unity; its square is the chain parameter. -/
public noncomputable def typeDOddCartanKernelEquiv
    (m : ℕ) (hm : 4 ≤ m) (hodd : m % 2 = 1) :
    rootsOfUnity 4 k ≃* typeDCartanKernel (k := k) m :=
  MulEquiv.ofBijective (oddParameterMap (k := k) m hm hodd)
    ⟨oddParameterMap_injective (k := k) m hm hodd,
      oddParameterMap_surjective (k := k) m hm hodd
        (typeD_cartan_kernel_odd_coordinates (k := k) m hm hodd)⟩


/-! The final public leaf consumes the center-character/coroot-lattice bridge
as an explicit equivalence.  This keeps the geometric bridge separate from
the type `D` Cartan arithmetic and avoids importing `theorem_1_12_5`.
-/
public theorem typeD_universal_center_shape_core
    {K : Variety k} [AlgebraicGroup K]
    (m : ℕ)
    (_hK : IsSemisimpleAlgebraicGroup K)
    (_hSimple : IsSimpleAlgebraicGroup K)
    (_hType : HasRootSystemType K ⟨.D, m⟩)
    (_hValid : IsValidGeneratorTableClassification ⟨.D, m⟩)
    (hm : 4 ≤ m)
    (hCenter :
      Nonempty
        (Subgroup.center (Variety.Point K) ≃*
          typeDCartanKernel (k := k) m))
    (_hUniversal : IsUniversalVersion K) :
    HasCenterShape (K := K) (universalCenterShape ⟨.D, m⟩) := by
  rcases hCenter with ⟨eCenter⟩
  by_cases heven : m % 2 = 0
  · rw [show universalCenterShape ⟨.D, m⟩ = .productOfSecondRoots by
        simp [universalCenterShape, heven]]
    exact ⟨eCenter.trans (typeDEvenCartanKernelEquiv (k := k) m hm heven).symm⟩
  · have hodd : m % 2 = 1 := by omega
    rw [show universalCenterShape ⟨.D, m⟩ = .rootsOfUnity 4 by
        simp [universalCenterShape, hodd]]
    exact ⟨eCenter.trans (typeDOddCartanKernelEquiv (k := k) m hm hodd).symm⟩

end Theory.AlgebraicGroup
