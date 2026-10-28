module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaIndependence

/-!
# Minimal offender ratios across complementary modules

Fixed points split across invariant complements. Comparing the exact rational offender ratios cancels the common cardinal factors and forces equality of the fixed subgroups.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

/-- The global `m`-ratio factors across a complementary pair of invariant
submodules. -/
private theorem m_mul_card_eq_fixedQuotientCard_mul_of_isCompl
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsMulCommutative V] [MulDistribMulAction G V]
    (A : Subgroup G) (C U : Subgroup V) (hcompl : IsCompl C U)
    [IsInvariant A V C] [IsInvariant A V U] :
    m (G := G) (V := V) A * Nat.card A =
      fixedQuotientCard (G := G) (V := V) A C *
        fixedQuotientCard (G := G) (V := V) A U := by
  have hcomm : U ≤ Subgroup.centralizer (C : Set V) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (IsMulCommutative.is_comm (M := V)).comm c u
  have hcardV : Nat.card V = Nat.card C * Nat.card U := by
    rw [← natCard_sup_eq_mul_of_disjoint_of_le_centralizer
      C U hcompl.disjoint hcomm, hcompl.sup_eq_top]
    simp
  have hcardFixed : Nat.card (FixedPoints.subgroup A V) =
      Nat.card (↥(C ⊓ FixedPoints.subgroup A V)) *
        Nat.card (↥(U ⊓ FixedPoints.subgroup A V)) := by
    have hproduct := natCard_inf_fixedPoints_sup_eq_mul
      (A := A) C U hcompl.disjoint
    rw [hcompl.sup_eq_top, top_inf_eq] at hproduct
    exact hproduct
  unfold m fixedQuotientCard
  rw [hcardV, hcardFixed]
  have hCne : (Nat.card (↥(C ⊓ FixedPoints.subgroup A V)) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos
      (α := ↥(C ⊓ FixedPoints.subgroup A V))).ne'
  have hUne : (Nat.card (↥(U ⊓ FixedPoints.subgroup A V)) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos
      (α := ↥(U ⊓ FixedPoints.subgroup A V))).ne'
  have hAne : (Nat.card A : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := A)).ne'
  push_cast
  field_simp

/-- If an order-two subgroup and the ambient elementary abelian Sylow group
have the same `m`-value and the expected compatible powers of two on an
invariant complementary summand, then they have the same fixed points on
the other summand. -/
public theorem exponent_le_of_m_eq_of_pow_quotients
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsMulCommutative V] [MulDistribMulAction G V]
    (S T : Subgroup G) (C U : Subgroup V) (hTS : T ≤ S)
    (hcompl : IsCompl C U)
    [IsInvariant S V C] [IsInvariant S V U]
    [IsInvariant T V C] [IsInvariant T V U]
    (n k l : ℕ)
    (hScard : Nat.card S = 2 ^ (n + 1))
    (hTcard : Nat.card T = 2)
    (hm : m (G := G) (V := V) T = m (G := G) (V := V) S)
    (hqS : fixedQuotientCard (G := G) (V := V) S U =
      (2 : ℚ) ^ (n + k))
    (hqT : fixedQuotientCard (G := G) (V := V) T U =
      (2 : ℚ) ^ l) : k ≤ l := by
  have hfactorS := m_mul_card_eq_fixedQuotientCard_mul_of_isCompl
    S C U hcompl
  have hfactorT := m_mul_card_eq_fixedQuotientCard_mul_of_isCompl
    T C U hcompl
  have hpowNpos : (0 : ℚ) < 2 ^ n := pow_pos (by norm_num) n
  have hfactorS' :
      m (G := G) (V := V) S * (2 : ℚ) =
        fixedQuotientCard (G := G) (V := V) S C * 2 ^ k := by
    rw [hScard, hqS] at hfactorS
    push_cast at hfactorS
    have hcancel : (2 : ℚ) ^ n *
        (m (G := G) (V := V) S * 2) =
          2 ^ n * (fixedQuotientCard (G := G) (V := V) S C *
            2 ^ k) := by
      calc
        (2 : ℚ) ^ n * (m (G := G) (V := V) S * 2) =
            m (G := G) (V := V) S * 2 ^ (n + 1) := by
          rw [pow_succ]
          ring
        _ = fixedQuotientCard (G := G) (V := V) S C *
            2 ^ (n + k) := hfactorS
        _ = 2 ^ n *
            (fixedQuotientCard (G := G) (V := V) S C * 2 ^ k) := by
          rw [pow_add]
          ring
    exact mul_left_cancel₀ hpowNpos.ne' hcancel
  have hfactorT' :
      m (G := G) (V := V) S * (2 : ℚ) =
        fixedQuotientCard (G := G) (V := V) T C * 2 ^ l := by
    rw [hTcard, hqT, hm] at hfactorT
    norm_num at hfactorT
    exact hfactorT
  have hqEq : fixedQuotientCard (G := G) (V := V) T C * 2 ^ l =
      fixedQuotientCard (G := G) (V := V) S C * 2 ^ k :=
    hfactorT'.symm.trans hfactorS'
  have hfixLe : C ⊓ FixedPoints.subgroup S V ≤
      C ⊓ FixedPoints.subgroup T V :=
    inf_le_inf_left C (fixedPoints_subgroup_antitone G V hTS)
  have hfixCardLe : Nat.card (↥(C ⊓ FixedPoints.subgroup S V)) ≤
      Nat.card (↥(C ⊓ FixedPoints.subgroup T V)) :=
    Subgroup.card_le_of_le hfixLe
  have hqLe : fixedQuotientCard (G := G) (V := V) T C ≤
      fixedQuotientCard (G := G) (V := V) S C := by
    unfold fixedQuotientCard
    apply div_le_div_of_nonneg_left
    · exact_mod_cast (Nat.zero_le (Nat.card C))
    · exact_mod_cast Nat.card_pos
        (α := ↥(C ⊓ FixedPoints.subgroup S V))
    · exact_mod_cast hfixCardLe
  have hqSpos : 0 < fixedQuotientCard (G := G) (V := V) S C := by
    unfold fixedQuotientCard
    have hnum : (0 : ℚ) < Nat.card C := by
      exact_mod_cast Nat.card_pos (α := C)
    have hden : (0 : ℚ) <
        Nat.card (↥(C ⊓ FixedPoints.subgroup S V)) := by
      exact_mod_cast Nat.card_pos
        (α := ↥(C ⊓ FixedPoints.subgroup S V))
    exact div_pos hnum hden
  by_contra hnot
  have hlk : l < k := Nat.lt_of_not_ge hnot
  have hpLt : (2 : ℚ) ^ l < 2 ^ k :=
    pow_lt_pow_right₀ (by norm_num) hlk
  have hleftLe : fixedQuotientCard (G := G) (V := V) T C * 2 ^ l ≤
      fixedQuotientCard (G := G) (V := V) S C * 2 ^ l :=
    mul_le_mul_of_nonneg_right hqLe (le_of_lt (pow_pos (by norm_num) l))
  have hrightLt : fixedQuotientCard (G := G) (V := V) S C * 2 ^ l <
      fixedQuotientCard (G := G) (V := V) S C * 2 ^ k :=
    mul_lt_mul_of_pos_left hpLt hqSpos
  exact (not_lt_of_ge (hqEq.ge.trans hleftLe)) hrightLt

public theorem inf_fixedPoints_eq_of_m_eq_of_pow_quotients
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsMulCommutative V] [MulDistribMulAction G V]
    (S T : Subgroup G) (C U : Subgroup V) (hTS : T ≤ S)
    (hcompl : IsCompl C U)
    [IsInvariant S V C] [IsInvariant S V U]
    [IsInvariant T V C] [IsInvariant T V U]
    (n k : ℕ)
    (hScard : Nat.card S = 2 ^ (n + 1))
    (hTcard : Nat.card T = 2)
    (hm : m (G := G) (V := V) T = m (G := G) (V := V) S)
    (hqS : fixedQuotientCard (G := G) (V := V) S U =
      (2 : ℚ) ^ (n + k))
    (hqT : fixedQuotientCard (G := G) (V := V) T U =
      (2 : ℚ) ^ k) :
    C ⊓ FixedPoints.subgroup S V =
      C ⊓ FixedPoints.subgroup T V := by
  have hfactorS := m_mul_card_eq_fixedQuotientCard_mul_of_isCompl
    S C U hcompl
  have hfactorT := m_mul_card_eq_fixedQuotientCard_mul_of_isCompl
    T C U hcompl
  have hpowNpos : (0 : ℚ) < 2 ^ n := pow_pos (by norm_num) n
  have hpowKpos : (0 : ℚ) < 2 ^ k := pow_pos (by norm_num) k
  have hfactorS' :
      m (G := G) (V := V) S * (2 : ℚ) =
        fixedQuotientCard (G := G) (V := V) S C * 2 ^ k := by
    rw [hScard, hqS] at hfactorS
    push_cast at hfactorS
    have hcancel : (2 : ℚ) ^ n *
        (m (G := G) (V := V) S * 2) =
          2 ^ n * (fixedQuotientCard (G := G) (V := V) S C *
            2 ^ k) := by
      calc
        (2 : ℚ) ^ n * (m (G := G) (V := V) S * 2) =
            m (G := G) (V := V) S * 2 ^ (n + 1) := by
          rw [pow_succ]
          ring
        _ = fixedQuotientCard (G := G) (V := V) S C *
            2 ^ (n + k) := hfactorS
        _ = 2 ^ n *
            (fixedQuotientCard (G := G) (V := V) S C * 2 ^ k) := by
          rw [pow_add]
          ring
    exact mul_left_cancel₀ hpowNpos.ne' hcancel
  have hfactorT' :
      m (G := G) (V := V) S * (2 : ℚ) =
        fixedQuotientCard (G := G) (V := V) T C * 2 ^ k := by
    rw [hTcard, hqT, hm] at hfactorT
    norm_num at hfactorT
    exact hfactorT
  have hqC : fixedQuotientCard (G := G) (V := V) S C =
      fixedQuotientCard (G := G) (V := V) T C := by
    nlinarith
  have hle : C ⊓ FixedPoints.subgroup S V ≤
      C ⊓ FixedPoints.subgroup T V := by
    exact inf_le_inf_left C
      (fixedPoints_subgroup_antitone G V hTS)
  have hCpos : (0 : ℚ) < Nat.card C := by
    exact_mod_cast Nat.card_pos (α := C)
  have hcardEq : Nat.card (↥(C ⊓ FixedPoints.subgroup S V)) =
      Nat.card (↥(C ⊓ FixedPoints.subgroup T V)) := by
    unfold fixedQuotientCard at hqC
    have hSpos : (0 : ℚ) <
        Nat.card (↥(C ⊓ FixedPoints.subgroup S V)) := by
      exact_mod_cast Nat.card_pos
        (α := ↥(C ⊓ FixedPoints.subgroup S V))
    have hTpos : (0 : ℚ) <
        Nat.card (↥(C ⊓ FixedPoints.subgroup T V)) := by
      exact_mod_cast Nat.card_pos
        (α := ↥(C ⊓ FixedPoints.subgroup T V))
    have hcross : (Nat.card C : ℚ) *
          Nat.card (↥(C ⊓ FixedPoints.subgroup T V)) =
        Nat.card C *
          Nat.card (↥(C ⊓ FixedPoints.subgroup S V)) := by
      exact (div_eq_div_iff
        (show (Nat.card (↥(C ⊓ FixedPoints.subgroup S V)) : ℚ) ≠ 0
          from hSpos.ne')
        (show (Nat.card (↥(C ⊓ FixedPoints.subgroup T V)) : ℚ) ≠ 0
          from hTpos.ne')).mp hqC
    have hcastEq : (Nat.card (↥(C ⊓ FixedPoints.subgroup S V)) : ℚ) =
        Nat.card (↥(C ⊓ FixedPoints.subgroup T V)) := by
      nlinarith
    exact_mod_cast hcastEq
  exact Subgroup.eq_of_le_of_card_ge hle hcardEq.ge

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
