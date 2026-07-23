/-
Authors: OpenAI
-/

module

public import Submission.FeitThompson.BGsection10.corollary_10_7_d
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

open scoped Pointwise

/-!
# Statements from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Corollary 10.7(e). -/
public theorem corollary_10_7_e
    {p : Nat.Primes} (P : Sylow p.val G) {R Q : Subgroup G}
    (hRp : IsPGroup p.val R) (hQle : Q ≤ (P : Subgroup G) ⊓ R)
    (hQnorm : section10NormalIn Q (Subgroup.normalizer ((P : Subgroup G) : Set G))) :
    section10NormalIn Q (Subgroup.normalizer (R : Set G)) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hQP : Q ≤ (P : Subgroup G) := by
    intro q hq
    exact (hQle hq).1
  have hQR : Q ≤ R := by
    intro q hq
    exact (hQle hq).2
  have hQ_le_NR : Q ≤ Subgroup.normalizer (R : Set G) := by
    intro q hq
    exact Subgroup.le_normalizer (hQR hq)
  have hNP_le_NQ :
      Subgroup.normalizer (((P : Subgroup G) : Set G)) ≤
        Subgroup.normalizer (Q : Set G) :=
    section10_normalIn_le_normalizer hQnorm
  obtain ⟨S, hRleS⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hRp
  obtain ⟨x, hxS⟩ := MulAction.exists_smul_eq G S P
  have hSxP : (S : Subgroup G).conjBy x = (P : Subgroup G) := by
    have hxS' := congrArg (fun T : Sylow p.val G => (T : Subgroup G)) hxS
    simpa [Subgroup.conjBy] using hxS'
  have hRxP : R.conjBy x ≤ (P : Subgroup G) := by
    exact (section10_conjBy_mono hRleS x).trans (le_of_eq hSxP)
  have hQxP : Q.conjBy x ≤ (P : Subgroup G) := by
    exact (section10_conjBy_mono hQR x).trans hRxP
  have hQx_eq_Q : Q.conjBy x = Q := by
    rcases corollary_10_7_c (G := G) P hQP hQxP with ⟨y, hQx_eq_Qy⟩
    have hQy_eq_Q : Q.conjBy (y : G) = Q :=
      section10_conjBy_eq_of_mem_normalizer (hNP_le_NQ y.property)
    exact hQx_eq_Qy.trans hQy_eq_Q
  have hxNQ : x ∈ Subgroup.normalizer (Q : Set G) :=
    section10_mem_normalizer_of_conjBy_eq hQx_eq_Q
  have hxinvQ : Q.conjBy x⁻¹ = Q :=
    section10_conjBy_eq_of_mem_normalizer
      ((Subgroup.normalizer (Q : Set G)).inv_mem hxNQ)
  have hNR_le_NQ :
      Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
    intro y hy
    have hRy_eq_R : R.conjBy y = R :=
      section10_conjBy_eq_of_mem_normalizer hy
    have hQyR : Q.conjBy y ≤ R := by
      exact (section10_conjBy_mono hQR y).trans (le_of_eq hRy_eq_R)
    have hQxyP : Q.conjBy (x * y) ≤ (P : Subgroup G) := by
      calc
        Q.conjBy (x * y) = (Q.conjBy y).conjBy x := section10_conjBy_mul Q x y
        _ ≤ R.conjBy x := section10_conjBy_mono hQyR x
        _ ≤ (P : Subgroup G) := hRxP
    have hQxy_eq_Q : Q.conjBy (x * y) = Q := by
      rcases corollary_10_7_c (G := G) P hQP hQxyP with ⟨z, hQxy_eq_Qz⟩
      have hQz_eq_Q : Q.conjBy (z : G) = Q :=
        section10_conjBy_eq_of_mem_normalizer (hNP_le_NQ z.property)
      exact hQxy_eq_Qz.trans hQz_eq_Q
    have hQy_eq_Q : Q.conjBy y = Q := by
      calc
        Q.conjBy y = (Q.conjBy (x * y)).conjBy x⁻¹ := by
          rw [section10_conjBy_mul Q x y]
          exact (section10_conjBy_inv (Q.conjBy y) x).symm
        _ = Q.conjBy x⁻¹ := by rw [hQxy_eq_Q]
        _ = Q := hxinvQ
    exact section10_mem_normalizer_of_conjBy_eq hQy_eq_Q
  exact section10_normalIn_of_le_normalizer hQ_le_NR hNR_le_NQ
