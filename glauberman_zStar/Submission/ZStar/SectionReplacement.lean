import Submission.ZStar.Constancy
import Submission.ZStar.OddCore

/-!
# The non-modular part of Feit XII.8.8

This file isolates the group-theoretic construction behind the commuting
replacement lemma.  The only character-theoretic input left abstract is the
specialized generalized-decomposition consequence saying that a principal
block character has the same value at `z*v` and `z` when `v` belongs to the
odd core of the involution centralizer.
-/

noncomputable section

namespace Submission.ZStar

namespace SectionReplacement

universe u

open Subgroup

/-- The group-theoretic and induction part of Feit XII.8.8.

The hypothesis `hproperCoreCentral` is the proper-subgroup induction
statement `t ∈ Z*(H)`, expressed as membership of each commutator in the
image of `O_{2'}(H)`.  The hypothesis `hsection` is the one remaining modular
input (Glauberman Lemmas 4 and 5). -/
theorem exists_commuting_replacement_of_section_invariance
    {G : Type u} [Group G] [Finite G]
    (f : Representation.ClassFunction G)
    (t s : G) (htI : IsInvolution t) (hsI : IsInvolution s)
    (hnotConj : ¬ IsConj s t)
    (hodd : ∀ g : G, Odd (orderOf ((g * t * g⁻¹) * t)))
    (hcentralizerProper : ∀ z : G, IsInvolution z →
      Subgroup.centralizer ({z} : Set G) ≠ ⊤)
    (hproperCoreCentral : ∀ (H : Subgroup G), H ≠ ⊤ → t ∈ H →
      ∀ h : G, h ∈ H →
        h * t * h⁻¹ * t⁻¹ ∈ (pPrimeCore 2 H).map H.subtype)
    (hsection : ∀ z : G, IsInvolution z → ∀ v : G,
      v ∈ (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype →
      f (ConjClasses.mk (z * v)) = f (ConjClasses.mk z)) :
    ∃ s0 : G, s0 ∈ (ConjClasses.mk s).carrier ∧ Commute t s0 ∧
      f (ConjClasses.mk (t * s)) = f (ConjClasses.mk (t * s0)) := by
  have ht_inv : t⁻¹ = t :=
    inv_eq_self_of_sq_eq_one (by simpa [pow_two] using htI.2)
  have hs_inv : s⁻¹ = s :=
    inv_eq_self_of_sq_eq_one (by simpa [pow_two] using hsI.2)
  have hst_ne : s ≠ t := by
    intro hst
    apply hnotConj
    rw [hst]
  let w : G := s * t
  have horder_even : Even (orderOf w) := by
    rw [← Nat.not_odd_iff_even]
    intro horder_odd
    obtain ⟨y, hyt, _⟩ :=
      OddCommutators.exists_conjugator_of_involutions_mul_odd hsI htI
        (by simpa [w] using horder_odd)
    apply hnotConj
    exact (isConj_iff.mpr ⟨y, hyt⟩).symm
  rcases horder_even with ⟨m, hm⟩
  have horder : orderOf w = 2 * m := by
    calc
      orderOf w = m + m := hm
      _ = 2 * m := by omega
  obtain ⟨hcI, hcs, hct⟩ :=
    BenderSuzuki.External.Suzuki.V.suzuki_ch5_proposition_1_2_iii
      (show BenderSuzuki.PFAppendixIII.IsInvolution s from ⟨hsI.1, hsI.2⟩)
      (show BenderSuzuki.PFAppendixIII.IsInvolution t from ⟨htI.1, htI.2⟩)
      hst_ne (by simpa [w] using horder)
  let c : G := w ^ m
  have hcI' : IsInvolution c := by
    exact ⟨by simpa [c, w] using hcI.ne_one,
      by simpa [c, w] using hcI.sq_eq_one⟩
  have hcs' : Commute c s := by simpa [c, w] using hcs
  have hct' : Commute c t := by simpa [c, w] using hct
  obtain ⟨a, hma | hma⟩ := m.even_or_odd'
  · let r : G := c * t
    have hr_conj_t : r = w ^ a * t * (w ^ a)⁻¹ := by
      dsimp [r, c]
      rw [hma]
      exact (OddCommutators.conjugate_second_by_product_pow
        (show BenderSuzuki.PFAppendixIII.IsInvolution s from ⟨hsI.1, hsI.2⟩)
        (show BenderSuzuki.PFAppendixIII.IsInvolution t from ⟨htI.1, htI.2⟩)
        a).symm
    have hrt_odd : Odd (orderOf (r * t)) := by
      rw [hr_conj_t]
      simpa [mul_assoc] using hodd (w ^ a)
    have hrt_eq_c : r * t = c := by
      dsimp [r]
      have htt : t * t = 1 := by simpa [pow_two] using htI.2
      rw [mul_assoc, htt, mul_one]
    rw [hrt_eq_c] at hrt_odd
    have hc_order : orderOf c = 2 := orderOf_eq_prime hcI'.2 hcI'.1
    rw [hc_order] at hrt_odd
    norm_num at hrt_odd
  · let s0 : G := c * t
    have hs0_conj_s : s0 = w ^ a * s * (w ^ a)⁻¹ := by
      dsimp [s0, c]
      rw [hma]
      exact (OddCommutators.conjugate_first_by_product_pow
        (show BenderSuzuki.PFAppendixIII.IsInvolution s from ⟨hsI.1, hsI.2⟩)
        (show BenderSuzuki.PFAppendixIII.IsInvolution t from ⟨htI.1, htI.2⟩)
        a).symm
    have hs0mem : s0 ∈ (ConjClasses.mk s).carrier := by
      apply ConjClasses.mem_carrier_iff_mk_eq.mpr
      apply ConjClasses.mk_eq_mk_iff_isConj.mpr
      apply isConj_iff.mpr
      exact ⟨(w ^ a)⁻¹, by simpa [hs0_conj_s, mul_assoc]⟩
    have hts0 : Commute t s0 := by
      dsimp [s0]
      show t * (c * t) = (c * t) * t
      calc
        t * (c * t) = (t * c) * t := by rw [mul_assoc]
        _ = (c * t) * t := by rw [hct'.eq.symm]
    have hts0_eq_c : t * s0 = c := hts0.eq.trans (by
      dsimp [s0]
      have htt : t * t = 1 := by simpa [pow_two] using htI.2
      rw [mul_assoc, htt, mul_one])
    let C : Subgroup G := Subgroup.centralizer ({c} : Set G)
    have htC : t ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hct'.eq.symm
    have hsC : s ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcs'.eq.symm
    have hCproper : C ≠ ⊤ := by
      simpa [C] using hcentralizerProper c hcI'
    have hw2Core : w ^ 2 ∈ (pPrimeCore 2 C).map C.subtype := by
      have hcomm := hproperCoreCentral C hCproper htC s hsC
      simpa [w, hs_inv, ht_inv, pow_two, mul_assoc] using hcomm
    let v : G := w ^ (m + 1)
    have hvCore : v ∈ (pPrimeCore 2 C).map C.subtype := by
      have hpow := ((pPrimeCore 2 C).map C.subtype).pow_mem hw2Core (a + 1)
      have hv_eq : v = (w ^ 2) ^ (a + 1) := by
        calc
          v = w ^ (2 * (a + 1)) := by
            dsimp [v]
            rw [hma]
            congr 1
          _ = (w ^ 2) ^ (a + 1) := by rw [pow_mul]
      rwa [← hv_eq] at hpow
    have hcv : c * v = w := by
      dsimp [c, v]
      rw [← pow_add]
      have hexponent : m + (m + 1) = orderOf w + 1 := by omega
      rw [hexponent, pow_succ, pow_orderOf_eq_one, one_mul]
    have hsection' : f (ConjClasses.mk (c * v)) = f (ConjClasses.mk c) := by
      apply hsection c hcI' v
      simpa [C] using hvCore
    have hts_conj_w : ConjClasses.mk (t * s) = ConjClasses.mk w := by
      apply ConjClasses.mk_eq_mk_iff_isConj.mpr
      apply isConj_iff.mpr
      refine ⟨t, ?_⟩
      dsimp [w]
      have htt : t * t = 1 := by simpa [pow_two] using htI.2
      rw [ht_inv]
      calc
        t * (t * s) * t = (t * t) * s * t := by group
        _ = s * t := by rw [htt, one_mul]
    refine ⟨s0, hs0mem, hts0, ?_⟩
    calc
      f (ConjClasses.mk (t * s)) = f (ConjClasses.mk w) := by rw [hts_conj_w]
      _ = f (ConjClasses.mk (c * v)) := by rw [hcv]
      _ = f (ConjClasses.mk c) := hsection'
      _ = f (ConjClasses.mk (t * s0)) := by rw [hts0_eq_c]

end SectionReplacement

end Submission.ZStar
