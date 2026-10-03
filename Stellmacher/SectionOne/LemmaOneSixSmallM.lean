module

public import Stellmacher.SectionOne.SmallMProof.QuotientAction
public import Stellmacher.SectionOne.SmallMProof.RecursiveData
public import Stellmacher.SectionOne.SmallMProof.ProductData

/-!
# Stellmacher (1.6) in the offender range

Induct on the Sylow subgroup order. The order-two classification is the base case. Each higher-rank local quotient has smaller Sylow order and m=1, so the restricted induction closes. Its local odd cores generate the global three-group; m(S)≤1 rules out nongeneric factors, and the proved generic alternatives finish the classification. The companion theorem extracts the SL2 alternative needed by (1.7).

The standing Section 1 hypotheses and subgroup/cardinality conditions are
explicit. This is the recursive proof used for the restricted conclusion
`m(S) ≤ 1`; the unrestricted source-facing theorem is not used.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.17–19,
and its offender application in (1.7).
-/

open scoped BigOperators Pointwise commutatorElement

namespace Stellmacher.SectionOne

universe u

open SmallMProof RankOneThreeGroupAssembly

private theorem initial_reduction
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS_elem : IsElementaryAbelian 2 (S : Subgroup G)) :
    (Nat.card (S : Subgroup G) = 2 ∧
        m (G := G) (V := V) (S : Subgroup G) > 1) ∨
      (Nat.card (S : Subgroup G) = 2 ∧
        m (G := G) (V := V) (S : Subgroup G) = 1) ∨
      4 ≤ Nat.card (S : Subgroup G) := by
  have hm_ge : 1 ≤ m (G := G) (V := V) (S : Subgroup G) :=
    (lemma_one_five h S (S : Subgroup G) le_rfl).part_e hS_elem
  rcases sylow_two_card_eq_two_or_ge_four h.G_even S with hcard | hcard
  · by_cases hm : m (G := G) (V := V) (S : Subgroup G) > 1
    · exact Or.inl ⟨hcard, hm⟩
    · exact Or.inr (Or.inl ⟨hcard, le_antisymm (not_lt.mp hm) hm_ge⟩)
  · exact Or.inr (Or.inr hcard)

public theorem lemma_one_six_of_m_le_one
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS_elem : IsElementaryAbelian 2 (S : Subgroup G))
    (hW : oddCore G = ⁅oddCore G, (S : Subgroup G)⁆)
    (hmin : ∀ Y : Subgroup G, Y ≤ (S : Subgroup G) → Y ≠ ⊥ →
      m (G := G) (V := V) (S : Subgroup G) ≤ m (G := G) (V := V) Y)
    (hm : m (G := G) (V := V) (S : Subgroup G) ≤ 1) :
    LemmaOneSixConclusion (G := G) (V := V) (S : Subgroup G) := by
  let rec aux
      {G₁ V₁ : Type u} [Group G₁] [Group V₁] [Finite G₁] [Finite V₁]
      [IsElementaryAbelian 2 V₁] [MulDistribMulAction G₁ V₁]
      (h₁ : Hypotheses G₁ V₁) (T : Sylow 2 G₁)
      (hT_elem : IsElementaryAbelian 2 (T : Subgroup G₁))
      (hW₁ : oddCore G₁ = ⁅oddCore G₁, (T : Subgroup G₁)⁆)
      (hmin₁ : ∀ Y : Subgroup G₁, Y ≤ (T : Subgroup G₁) → Y ≠ ⊥ →
        m (G := G₁) (V := V₁) (T : Subgroup G₁) ≤
          m (G := G₁) (V := V₁) Y)
      (hm₁ : m (G := G₁) (V := V₁) (T : Subgroup G₁) ≤ 1) :
      LemmaOneSixConclusion (G := G₁) (V := V₁) (T : Subgroup G₁) := by
    rcases initial_reduction h₁ T hT_elem with hsmall | hbase | hlarge
    · exact False.elim ((not_lt_of_ge hm₁) hsmall.2)
    · obtain ⟨hTcard, hmT⟩ := hbase
      exact order_two_odd_complement_classification
        h₁ T hT_elem hTcard hmT hW₁
    · have hind : ∀ {G₂ V₂ : Type u}
          [Group G₂] [Group V₂] [Finite G₂] [Finite V₂]
          [IsElementaryAbelian 2 V₂] [MulDistribMulAction G₂ V₂],
          (h₂ : Hypotheses G₂ V₂) → (R : Sylow 2 G₂) →
          (hR : IsElementaryAbelian 2 (R : Subgroup G₂)) →
          (hW₂ : oddCore G₂ = ⁅oddCore G₂, (R : Subgroup G₂)⁆) →
          (∀ Y : Subgroup G₂, Y ≤ (R : Subgroup G₂) → Y ≠ ⊥ →
            m (G := G₂) (V := V₂) (R : Subgroup G₂) ≤
              m (G := G₂) (V := V₂) Y) →
          m (G := G₂) (V := V₂) (R : Subgroup G₂) ≤ 1 →
          Nat.card (R : Subgroup G₂) < Nat.card (T : Subgroup G₁) →
          LemmaOneSixConclusion (G := G₂) (V := V₂)
            (R : Subgroup G₂) := by
        intro G₂ V₂ _ _ _ _ _ _ h₂ R hR hW₂ hmin₂ hm₂ hlt
        exact aux h₂ R hR hW₂ hmin₂ hm₂
      have hlocal : RankOneAssemblyLocalHypothesis
          (G := G₁) (V := V₁) (T : Subgroup G₁) :=
        local_recursive_sl2_assembly_hypothesis
          h₁ T hT_elem hlarge hmin₁ hind
      have hW3 : IsPGroup 3 (oddCore G₁) :=
        oddCore_isPGroup_three_of_local_commutators
          h₁ T hT_elem hlarge hW₁ (fun A hAmax hAcard =>
          local_WA_isPGroup_three
            h₁ T hT_elem hlarge hmin₁ A hAmax hAcard hind)
      have hgeneric : RankOneAssemblyGenericHypothesis
          (G := G₁) (V := V₁) (T : Subgroup G₁) :=
        generic_of_m_lt_two (T : Subgroup G₁) hT_elem (lt_of_le_of_lt hm₁ (by norm_num))
      rcases generic_rank_one_three_group_alternatives
          h₁ T hT_elem hlarge hW₁ hW3 hmin₁ hlocal hgeneric with
        ⟨hprod, hquad, hfixed⟩ | ⟨hprod, hquad, hfixed⟩
      · exact LemmaOneSixConclusion.omegaProduct hprod hquad hfixed
      · exact LemmaOneSixConclusion.sl2Product hprod hquad hfixed
  termination_by Nat.card (T : Subgroup G₁)
  exact aux h S hS_elem hW hmin hm

/-- In the offender range, the classification gives the exact local SL2 product data. -/

public theorem lemma_one_six_sl2_of_m_le_one
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS_elem : IsElementaryAbelian 2 (S : Subgroup G))
    (hW : oddCore G = ⁅oddCore G, (S : Subgroup G)⁆)
    (hmin : ∀ Y : Subgroup G, Y ≤ (S : Subgroup G) → Y ≠ ⊥ →
      m (G := G) (V := V) (S : Subgroup G) ≤ m (G := G) (V := V) Y)
    (hm : m (G := G) (V := V) (S : Subgroup G) ≤ 1) :
    RankOneLocalSL2Data (G := G) (V := V) (S : Subgroup G) := by
  have hmEq : m (G := G) (V := V) (S : Subgroup G) = 1 :=
    le_antisymm hm ((lemma_one_five h S (S : Subgroup G) le_rfl).part_e hS_elem)
  exact SmallMProof.sl2Data_of_conclusion_of_m_eq_one (S : Subgroup G) hmEq
    (lemma_one_six_of_m_le_one h S hS_elem hW hmin hm)

end Stellmacher.SectionOne
