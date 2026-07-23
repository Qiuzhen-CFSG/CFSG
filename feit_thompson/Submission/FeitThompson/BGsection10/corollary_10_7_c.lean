/-
Authors: OpenAI
-/

module

public import FeitThompson.BGsection10.corollary_10_7_b
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

/-- Corollary 10.7(c). -/
public theorem corollary_10_7_c
    {p : Nat.Primes} (P : Sylow p.val G) {Q : Subgroup G}
    (hQle : Q ≤ (P : Subgroup G)) {x : G} (hQx : Q.conjBy x ≤ (P : Subgroup G)) :
    ∃ y : Subgroup.normalizer ((P : Subgroup G) : Set G), Q.conjBy x = Q.conjBy (y : G) := by
  classical
  by_cases hQbot : Q = ⊥
  · refine ⟨⟨1, by simp⟩, ?_⟩
    simp [hQbot, Subgroup.conjBy]
  · haveI : Fact p.val.Prime := ⟨p.property⟩
    have hPne : (P : Subgroup G) ≠ ⊥ := by
      intro hPbot
      apply hQbot
      exact le_bot_iff.mp (by simpa [hPbot] using hQle)
    let N : Subgroup G := Subgroup.normalizer (((P : Subgroup G) : Set G))
    have hNproper : N ≠ ⊤ := by
      simpa [N] using section10_sylow_normalizer_ne_top_of_ne_bot (G := G) P hPne
    obtain ⟨M, hMcont⟩ :=
      section10_exists_maximalSubgroupsContaining_of_ne_top (G := G) hNproper
    have hM : M ∈ section9MaximalSubgroups G := hMcont.1
    have hNM : N ≤ M := hMcont.2
    have hP_le_N : (P : Subgroup G) ≤ N := by
      simpa [N] using (Subgroup.le_normalizer : (P : Subgroup G) ≤
        Subgroup.normalizer (((P : Subgroup G) : Set G)))
    have hP_le_M : (P : Subgroup G) ≤ M := hP_le_N.trans hNM
    let PM : Sylow p.val M := P.subtype hP_le_M
    have hPMmap : (PM : Subgroup M).map M.subtype = (P : Subgroup G) := by
      simpa [PM, Sylow.subtype] using
        (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := (P : Subgroup G)) (K := M) hP_le_M)
    have hp_dvd_P : p.val ∣ Nat.card (P : Subgroup G) := by
      rcases P.isPGroup'.card_eq_or_dvd with hcard | hdiv
      · exact False.elim (hPne ((Subgroup.card_eq_one (H := (P : Subgroup G))).mp hcard))
      · exact hdiv
    have hpM : p ∈ subgroupPrimeSet M := by
      simpa [subgroupPrimeSet] using hp_dvd_P.trans (Subgroup.card_dvd_of_le hP_le_M)
    have hpσ : p ∈ section10SigmaPrimes M := by
      refine ⟨hpM, PM, ?_⟩
      simpa [section10AmbientSylowSubgroup, hPMmap, N] using hNM
    have hQM : Q ≤ M := hQle.trans hP_le_M
    have hQp : IsPGroup p.val Q :=
      IsPGroup.to_le (H := Q) (K := (P : Subgroup G)) P.isPGroup' hQle
    have hQxM : Q.conjBy x ≤ M := hQx.trans hP_le_M
    rcases theorem_10_1_a (G := G) (M := M) (X := Q) (p := p)
        hM hpσ hQbot hQp hQM hQxM with ⟨m, c, hx_eq⟩
    have hQx_eq_Qm : Q.conjBy x = Q.conjBy (m : G) := by
      calc
        Q.conjBy x = Q.conjBy ((m : G) * (c : G)) := by rw [hx_eq]
        _ = (Q.conjBy (c : G)).conjBy (m : G) :=
          section10_conjBy_mul Q (m : G) (c : G)
        _ = Q.conjBy (m : G) := by
          rw [section10_conjBy_eq_of_mem_normalizer
            (H := Q) (g := (c : G)) (centralizer_le_normalizer Q c.property)]
    have hQmP : Q.conjBy (m : G) ≤ (P : Subgroup G) := by
      intro z hz
      exact hQx (by simpa [hQx_eq_Qm] using hz)
    haveI : IsSolvable M :=
      IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
    have hplM : HasPLengthOne p.val M :=
      theorem_10_6 (G := G) (H := M) (p := p) hM.1
    let QM : Subgroup M := Q.subgroupOf M
    let Y : Set M := (QM : Set M)
    haveI : Nonempty Y := ⟨⟨1, by simp [Y, QM]⟩⟩
    have hYle : Y ⊆ (PM : Subgroup M) := by
      intro y hy
      have hyQ : (y : G) ∈ Q := by
        simpa [Y, QM, Subgroup.mem_subgroupOf] using hy
      have hyP : (y : G) ∈ (P : Subgroup G) := hQle hyQ
      simpa [PM, Sylow.subtype, Subgroup.mem_subgroupOf] using hyP
    have hmY : ∀ y ∈ Y, m * y * m⁻¹ ∈ (PM : Subgroup M) := by
      intro y hy
      have hyQ : (y : G) ∈ Q := by
        simpa [Y, QM, Subgroup.mem_subgroupOf] using hy
      have hconjQ : (m : G) * (y : G) * (m : G)⁻¹ ∈ Q.conjBy (m : G) := by
        rw [Subgroup.conjBy, Subgroup.mem_map]
        exact ⟨(y : G), hyQ, by simp [MulAut.conj_apply]⟩
      have hconjP : (m : G) * (y : G) * (m : G)⁻¹ ∈ (P : Subgroup G) :=
        hQmP hconjQ
      simpa [PM, Sylow.subtype, Subgroup.mem_subgroupOf, mul_assoc] using hconjP
    obtain ⟨cM, hcM, yM, hyMnorm, hyMcM_eq_m⟩ :=
      lemma_6_6_c (G := M) (p := p.val) hplM (S := PM) (Y := Y) hYle hmY
    have hQM_m_eq_yM : QM.conjBy m = QM.conjBy yM := by
      calc
        QM.conjBy m = QM.conjBy (yM * cM) := by rw [hyMcM_eq_m]
        _ = (QM.conjBy cM).conjBy yM :=
          section10_conjBy_mul (G := M) QM yM cM
        _ = QM.conjBy yM := by
          rw [section10_conjBy_eq_of_mem_normalizer
            (G := M) (H := QM) (g := cM) (centralizer_le_normalizer QM hcM)]
    have hNMmap :
        (Subgroup.normalizer (((PM : Subgroup M) : Set M))).map M.subtype = N := by
      simpa [PM, N] using
        section10_normalizer_map_subtype_eq_of_map_eq
          (G := G) (M := M) (P := (P : Subgroup G)) (Q := (PM : Subgroup M))
          hPMmap (by simpa [N] using hNM)
    have hyMnorm_ambient : ((yM : M) : G) ∈ N := by
      rw [← hNMmap]
      exact Subgroup.mem_map_of_mem M.subtype hyMnorm
    refine ⟨⟨((yM : M) : G), by simpa [N] using hyMnorm_ambient⟩, ?_⟩
    calc
      Q.conjBy x = Q.conjBy (m : G) := hQx_eq_Qm
      _ = (QM.conjBy m).map M.subtype := by
        rw [section10_subgroupOf_conjBy_map_subtype (G := G) hQM m]
      _ = (QM.conjBy yM).map M.subtype := by rw [hQM_m_eq_yM]
      _ = Q.conjBy ((yM : M) : G) := by
        rw [section10_subgroupOf_conjBy_map_subtype (G := G) hQM yM]
