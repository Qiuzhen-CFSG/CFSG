module

public import Stellmacher.SectionOne.SmallMProof.QuotientAction
public import Stellmacher.SectionOne.SmallMProof.QuotientSylow
public import Stellmacher.SectionOne.SmallMProof.LocalHypotheses

/-!
# The local equality m=1 and minimality

Lemma (1.5)(a) and global minimality cancel the offender ratios to show the quotient Sylow has m=1. The relative lower bound from (1.5)(e) proves minimality for every nontrivial subgroup of that Sylow subgroup.

The standing Section 1 hypotheses and subgroup/cardinality conditions are
explicit. This is the recursive proof used for the restricted conclusion
`m(S) ≤ 1`; the unrestricted source-facing theorem is not used.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.17–19,
and its offender application in (1.7).
-/

open scoped BigOperators Pointwise commutatorElement

namespace Stellmacher.SectionOne.SmallMProof

universe u

open RankOneThreeGroupAssembly

public theorem local_quotient_sylow_m_eq_one
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (A : Subgroup G)
    (hS_elem : IsElementaryAbelian 2 (S : Subgroup G))
    (hAmax : oneAmax (G := G) (V := V) (S : Subgroup G) A)
    (hAcard : Nat.card A = 2)
    (hmin : ∀ Y : Subgroup G, Y ≤ (S : Subgroup G) → Y ≠ ⊥ →
      m (G := G) (V := V) (S : Subgroup G) ≤ m (G := G) (V := V) Y) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), (S : Subgroup G)⁆
    let H := W_A ⊔ (S : Subgroup G)
    let S_H := (S : Subgroup G).subgroupOf H
    let A_H := A.subgroupOf H
    let _ : A_H.Normal := local_A_normal (S : Subgroup G) A hS_elem hAmax.1
    let _ : IsInvariant H V (FixedPoints.subgroup A_H V) :=
      fixedPoints_isInvariant_of_normal A_H
    let Pbar := S_H.map (QuotientGroup.mk' A_H)
    m (G := H ⧸ A_H) (V := FixedPoints.subgroup A_H V) Pbar = 1 := by
  classical
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), (S : Subgroup G)⁆
  let H := W_A ⊔ (S : Subgroup G)
  let S_H := (S : Subgroup G).subgroupOf H
  let A_H := A.subgroupOf H
  let : A_H.Normal :=
    local_A_normal (S : Subgroup G) A hS_elem hAmax.1
  let : IsInvariant H V (FixedPoints.subgroup A_H V) :=
    fixedPoints_isInvariant_of_normal A_H
  let Pbar := S_H.map (QuotientGroup.mk' A_H)
  have hAne : A ≠ ⊥ := by
    intro hAbot
    rw [hAbot] at hAcard
    simp at hAcard
  have hmEq : m (G := G) (V := V) A =
      m (G := G) (V := V) (S : Subgroup G) :=
    le_antisymm hAmax.2.1 (hmin A hAmax.1 hAne)
  have hmPos : 0 < m (G := G) (V := V) (S : Subgroup G) :=
    lt_of_lt_of_le zero_lt_one
      ((lemma_one_five h S (S : Subgroup G) le_rfl).part_e hS_elem)
  have hmNe : m (G := G) (V := V) (S : Subgroup G) ≠ 0 := ne_of_gt hmPos
  have hratio := (lemma_one_five h S A hAmax.1).part_a
  have hratio' : subgroupQuotientCard
      (FixedPoints.subgroup A V) (FixedPoints.subgroup (S : Subgroup G) V) =
      (indexWithin (S : Subgroup G) A : ℚ) := by
    simpa [hmEq, hmNe] using hratio
  have hfixedCard : Nat.card (FixedPoints.subgroup A V) =
      Nat.card (FixedPoints.subgroup (S : Subgroup G) V) *
        indexWithin (S : Subgroup G) A := by
    unfold subgroupQuotientCard at hratio'
    have hden : (Nat.card (FixedPoints.subgroup (S : Subgroup G) V) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos
        (α := FixedPoints.subgroup (S : Subgroup G) V)).ne'
    have hcast := (div_eq_iff hden).mp hratio'
    exact_mod_cast hcast.trans (mul_comm _ _)
  have hVAcard : Nat.card (FixedPoints.subgroup A_H V) =
      Nat.card (FixedPoints.subgroup A V) := by
    exact Nat.card_congr {
      toFun := fun v => ⟨(v : V), by
        rw [FixedPoints.mem_subgroup]
        intro a
        exact (FixedPoints.mem_subgroup (M := A_H) (a := (v : V))).1 v.property
          ⟨⟨a, (hAmax.1.trans (show (S : Subgroup G) ≤ H from le_sup_right))
              a.property⟩,
            a.property⟩⟩
      invFun := fun v => ⟨(v : V), by
        rw [FixedPoints.mem_subgroup]
        intro a
        exact (FixedPoints.mem_subgroup (M := A) (a := (v : V))).1 v.property
          ⟨(a : G), a.property⟩⟩
      left_inv := fun v => rfl
      right_inv := fun v => rfl }
  have hPcard : Nat.card Pbar = indexWithin (S : Subgroup G) A :=
    local_quotient_sylow_card_eq_index (S : Subgroup G) A hS_elem hAmax.1
  have hFP : FixedPoints.subgroup Pbar (FixedPoints.subgroup A_H V) =
      FixedPoints.subgroup S_H (FixedPoints.subgroup A_H V) :=
    local_quotient_fixedPoints_eq (S : Subgroup G) A hS_elem hAmax.1
  have hFPcard : Nat.card (FixedPoints.subgroup Pbar
      (FixedPoints.subgroup A_H V)) =
      Nat.card (FixedPoints.subgroup (S : Subgroup G) V) := by
    rw [hFP]
    exact local_fixedPoints_card_eq (S : Subgroup G) A hS_elem hAmax.1
  change m (G := H ⧸ A_H) (V := FixedPoints.subgroup A_H V) Pbar = 1
  unfold m
  rw [hVAcard, hfixedCard, hFPcard, hPcard]
  have hprod : (Nat.card (FixedPoints.subgroup (S : Subgroup G) V) : ℚ) *
      (indexWithin (S : Subgroup G) A : ℚ) ≠ 0 := by
    exact mul_ne_zero
      (by exact_mod_cast (Nat.card_pos
        (α := FixedPoints.subgroup (S : Subgroup G) V)).ne')
      (by
        exact_mod_cast
          (Subgroup.index_ne_zero_of_finite (H := A.subgroupOf (S : Subgroup G))))
  rw [Nat.cast_mul]
  exact div_self hprod

public theorem local_quotient_minimal_m
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (A : Subgroup G)
    (hS_elem : IsElementaryAbelian 2 (S : Subgroup G))
    (hAmax : oneAmax (G := G) (V := V) (S : Subgroup G) A)
    (hAcard : Nat.card A = 2) (hScard : 4 ≤ Nat.card (S : Subgroup G))
    (hmin : ∀ Y : Subgroup G, Y ≤ (S : Subgroup G) → Y ≠ ⊥ →
      m (G := G) (V := V) (S : Subgroup G) ≤ m (G := G) (V := V) Y) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), (S : Subgroup G)⁆
    let H := W_A ⊔ (S : Subgroup G)
    let A_H := A.subgroupOf H
    let _ : A_H.Normal := local_A_normal (S : Subgroup G) A hS_elem hAmax.1
    let V_A := FixedPoints.subgroup A_H V
    let _ : IsElementaryAbelian 2 V_A := isElementaryAbelian_subgroup V_A
    ∀ P : Sylow 2 (H ⧸ A_H),
      (P : Subgroup (H ⧸ A_H)) =
          ((S : Subgroup G).subgroupOf H).map (QuotientGroup.mk' A_H) →
      ∀ Y : Subgroup (H ⧸ A_H), Y ≤ (P : Subgroup (H ⧸ A_H)) → Y ≠ ⊥ →
        m (G := H ⧸ A_H) (V := V_A) (P : Subgroup (H ⧸ A_H)) ≤
          m (G := H ⧸ A_H) (V := V_A) Y := by
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), (S : Subgroup G)⁆
  let H := W_A ⊔ (S : Subgroup G)
  let A_H := A.subgroupOf H
  let : A_H.Normal :=
    local_A_normal (S : Subgroup G) A hS_elem hAmax.1
  let V_A := FixedPoints.subgroup A_H V
  let : IsElementaryAbelian 2 V_A := isElementaryAbelian_subgroup V_A
  let : IsInvariant H V V_A := fixedPoints_isInvariant_of_normal A_H
  have hlocal : Hypotheses (H ⧸ A_H) V_A :=
    local_quotient_hypotheses h (S : Subgroup G) A hS_elem hAmax hAcard hScard
  change ∀ P : Sylow 2 (H ⧸ A_H),
    (P : Subgroup (H ⧸ A_H)) =
        ((S : Subgroup G).subgroupOf H).map (QuotientGroup.mk' A_H) →
    ∀ Y : Subgroup (H ⧸ A_H), Y ≤ (P : Subgroup (H ⧸ A_H)) → Y ≠ ⊥ →
      m (G := H ⧸ A_H) (V := V_A) (P : Subgroup (H ⧸ A_H)) ≤
        m (G := H ⧸ A_H) (V := V_A) Y
  intro P hP Y hYP _hYne
  have hPelem : IsElementaryAbelian 2 (P : Subgroup (H ⧸ A_H)) := by
    rw [hP]
    let : IsElementaryAbelian 2 (S : Subgroup G) := hS_elem
    let : IsElementaryAbelian 2 ((S : Subgroup G).subgroupOf H) :=
      IsElementaryAbelian.subgroupOf (show (S : Subgroup G) ≤ H from le_sup_right)
    exact IsElementaryAbelian.map (QuotientGroup.mk' A_H)
  have hYelem : IsElementaryAbelian 2 Y :=
    isElementaryAbelian_of_le hPelem hYP
  have hPone : m (G := H ⧸ A_H) (V := V_A)
      (P : Subgroup (H ⧸ A_H)) = 1 := by
    rw [hP]
    exact local_quotient_sylow_m_eq_one h S A hS_elem hAmax hAcard hmin
  rw [hPone]
  exact lemma_one_five_m_ge_one_relative hlocal P Y hYP hYelem

end Stellmacher.SectionOne.SmallMProof
