module

public import Stellmacher.SectionOne.SmallMProof.QuotientAction
public import Stellmacher.SectionOne.SmallMProof.LocalCores
public import Stellmacher.SectionOne.SmallMProof.LocalHypotheses
public import Stellmacher.SectionOne.SmallMProof.QuotientSylow
public import Stellmacher.SectionOne.SmallMProof.LocalMinimality
public import Stellmacher.SectionOne.SmallMProof.ProductData

/-!
# The recursive local data with restricted induction

The quotient Sylow cardinality is strictly smaller. Its already-proved m=1 permits the restricted induction hypothesis; the resulting SL2 data retain the same factor family, odd-core image, cardinal preservation and full local m equality.

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

private theorem local_recursive_sl2_data
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS_elem : IsElementaryAbelian 2 (S : Subgroup G))
    (hScard : 4 ≤ Nat.card (S : Subgroup G))
    (hmin : ∀ Y : Subgroup G, Y ≤ (S : Subgroup G) → Y ≠ ⊥ →
      m (G := G) (V := V) (S : Subgroup G) ≤ m (G := G) (V := V) Y)
    (A : Subgroup G)
    (hAmax : oneAmax (G := G) (V := V) (S : Subgroup G) A)
    (hAcard : Nat.card A = 2)
    (hind : ∀ {G₁ V₁ : Type u} [Group G₁] [Group V₁] [Finite G₁] [Finite V₁]
      [IsElementaryAbelian 2 V₁] [MulDistribMulAction G₁ V₁],
      (h₁ : Hypotheses G₁ V₁) → (T : Sylow 2 G₁) →
      (hT : IsElementaryAbelian 2 (T : Subgroup G₁)) →
      (hW₁ : oddCore G₁ = ⁅oddCore G₁, (T : Subgroup G₁)⁆) →
      (∀ Y : Subgroup G₁, Y ≤ (T : Subgroup G₁) → Y ≠ ⊥ →
        m (G := G₁) (V := V₁) (T : Subgroup G₁) ≤
          m (G := G₁) (V := V₁) Y) →
      m (G := G₁) (V := V₁) (T : Subgroup G₁) ≤ 1 →
      Nat.card (T : Subgroup G₁) < Nat.card (S : Subgroup G) →
      LemmaOneSixConclusion (G := G₁) (V := V₁) (T : Subgroup G₁)) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), (S : Subgroup G)⁆
    let H := W_A ⊔ (S : Subgroup G)
    let A_H := A.subgroupOf H
    let _ : A_H.Normal := local_A_normal (S : Subgroup G) A hS_elem
      hAmax.1
    let V_A := FixedPoints.subgroup A_H V
    let _ : IsElementaryAbelian 2 V_A := isElementaryAbelian_subgroup V_A
    ∃ P : Sylow 2 (H ⧸ A_H),
      (P : Subgroup (H ⧸ A_H)) =
          ((S : Subgroup G).subgroupOf H).map (QuotientGroup.mk' A_H) ∧
        oddCore (H ⧸ A_H) =
          (W_A.subgroupOf H).map (QuotientGroup.mk' A_H) ∧
        Nat.card ((W_A.subgroupOf H).map (QuotientGroup.mk' A_H)) =
          Nat.card W_A ∧
        RankOneLocalSL2Data (G := H ⧸ A_H) (V := V_A)
          (P : Subgroup (H ⧸ A_H)) ∧
        m (G := H ⧸ A_H) (V := V_A) (P : Subgroup (H ⧸ A_H)) = 1 := by
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), (S : Subgroup G)⁆
  let H := W_A ⊔ (S : Subgroup G)
  let A_H := A.subgroupOf H
  let : A_H.Normal :=
    local_A_normal (S : Subgroup G) A hS_elem hAmax.1
  let V_A := FixedPoints.subgroup A_H V
  let : IsElementaryAbelian 2 V_A := isElementaryAbelian_subgroup V_A
  let : IsInvariant H V V_A := fixedPoints_isInvariant_of_normal A_H
  obtain ⟨P, hP, hPelem⟩ :=
    local_quotient_sylow_exists (S : Subgroup G) A hS_elem hAmax.1
  have hcoreData :=
    local_quotient_oddCore_commutator
      h (S : Subgroup G) A hS_elem hAmax.1
  refine ⟨P, hP, hcoreData.1, hcoreData.2.1, ?_⟩
  have hlocal : Hypotheses (H ⧸ A_H) V_A :=
    local_quotient_hypotheses h (S : Subgroup G) A hS_elem hAmax hAcard hScard
  have hWlocal : oddCore (H ⧸ A_H) =
      ⁅oddCore (H ⧸ A_H), (P : Subgroup (H ⧸ A_H))⁆ := by
    rw [hP]
    exact hcoreData.2.2
  have hminlocal : ∀ Y : Subgroup (H ⧸ A_H),
      Y ≤ (P : Subgroup (H ⧸ A_H)) → Y ≠ ⊥ →
      m (G := H ⧸ A_H) (V := V_A) (P : Subgroup (H ⧸ A_H)) ≤
        m (G := H ⧸ A_H) (V := V_A) Y :=
    local_quotient_minimal_m h S A hS_elem hAmax hAcard hScard hmin P hP
  have hPcard : Nat.card (P : Subgroup (H ⧸ A_H)) =
      indexWithin (S : Subgroup G) A := by
    rw [hP]
    exact local_quotient_sylow_card_eq_index (S : Subgroup G) A hS_elem hAmax.1
  have hindexMul := Subgroup.index_mul_card (H := A.subgroupOf (S : Subgroup G))
  rw [natCard_subgroupOf_eq A (S : Subgroup G) hAmax.1, hAcard] at hindexMul
  have hPlt : Nat.card (P : Subgroup (H ⧸ A_H)) <
      Nat.card (S : Subgroup G) := by
    rw [hPcard]
    change (A.subgroupOf (S : Subgroup G)).index < Nat.card (S : Subgroup G)
    omega
  have hmP : m (G := H ⧸ A_H) (V := V_A)
      (P : Subgroup (H ⧸ A_H)) = 1 := by
    rw [hP]
    exact local_quotient_sylow_m_eq_one h S A hS_elem hAmax hAcard hmin
  have hc := hind hlocal P hPelem hWlocal hminlocal (by rw [hmP]) hPlt
  exact ⟨sl2Data_of_conclusion_of_m_eq_one (P : Subgroup (H ⧸ A_H)) hmP hc, hmP⟩

public theorem local_recursive_sl2_assembly_hypothesis
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS_elem : IsElementaryAbelian 2 (S : Subgroup G))
    (hScard : 4 ≤ Nat.card (S : Subgroup G))
    (hmin : ∀ Y : Subgroup G, Y ≤ (S : Subgroup G) → Y ≠ ⊥ →
      m (G := G) (V := V) (S : Subgroup G) ≤ m (G := G) (V := V) Y)
    (hind : ∀ {G₁ V₁ : Type u} [Group G₁] [Group V₁] [Finite G₁] [Finite V₁]
      [IsElementaryAbelian 2 V₁] [MulDistribMulAction G₁ V₁],
      (h₁ : Hypotheses G₁ V₁) → (T : Sylow 2 G₁) →
      (hT : IsElementaryAbelian 2 (T : Subgroup G₁)) →
      (hW₁ : oddCore G₁ = ⁅oddCore G₁, (T : Subgroup G₁)⁆) →
      (∀ Y : Subgroup G₁, Y ≤ (T : Subgroup G₁) → Y ≠ ⊥ →
        m (G := G₁) (V := V₁) (T : Subgroup G₁) ≤
          m (G := G₁) (V := V₁) Y) →
      m (G := G₁) (V := V₁) (T : Subgroup G₁) ≤ 1 →
      Nat.card (T : Subgroup G₁) < Nat.card (S : Subgroup G) →
      LemmaOneSixConclusion (G := G₁) (V := V₁) (T : Subgroup G₁)) :
    RankOneAssemblyLocalHypothesis (G := G) (V := V) (S : Subgroup G) := by
  intro A hAmax hAcard
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), (S : Subgroup G)⁆
  let H := W_A ⊔ (S : Subgroup G)
  let A_H := A.subgroupOf H
  let hA_H : A_H.Normal := local_A_normal (S : Subgroup G) A hS_elem hAmax.1
  refine ⟨hA_H, ?_⟩
  exact local_recursive_sl2_data
    h S hS_elem hScard hmin A hAmax hAcard hind

public theorem local_WA_isPGroup_three
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS_elem : IsElementaryAbelian 2 (S : Subgroup G))
    (hScard : 4 ≤ Nat.card (S : Subgroup G))
    (hmin : ∀ Y : Subgroup G, Y ≤ (S : Subgroup G) → Y ≠ ⊥ →
      m (G := G) (V := V) (S : Subgroup G) ≤ m (G := G) (V := V) Y)
    (A : Subgroup G)
    (hAmax : oneAmax (G := G) (V := V) (S : Subgroup G) A)
    (hAcard : Nat.card A = 2)
    (hind : ∀ {G₁ V₁ : Type u} [Group G₁] [Group V₁] [Finite G₁] [Finite V₁]
      [IsElementaryAbelian 2 V₁] [MulDistribMulAction G₁ V₁],
      (h₁ : Hypotheses G₁ V₁) → (T : Sylow 2 G₁) →
      (hT : IsElementaryAbelian 2 (T : Subgroup G₁)) →
      (hW₁ : oddCore G₁ = ⁅oddCore G₁, (T : Subgroup G₁)⁆) →
      (∀ Y : Subgroup G₁, Y ≤ (T : Subgroup G₁) → Y ≠ ⊥ →
        m (G := G₁) (V := V₁) (T : Subgroup G₁) ≤
          m (G := G₁) (V := V₁) Y) →
      m (G := G₁) (V := V₁) (T : Subgroup G₁) ≤ 1 →
      Nat.card (T : Subgroup G₁) < Nat.card (S : Subgroup G) →
      LemmaOneSixConclusion (G := G₁) (V := V₁) (T : Subgroup G₁)) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), (S : Subgroup G)⁆
    IsPGroup 3 W_A := by
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), (S : Subgroup G)⁆
  let H := W_A ⊔ (S : Subgroup G)
  let A_H := A.subgroupOf H
  let : A_H.Normal := local_A_normal (S : Subgroup G) A hS_elem hAmax.1
  let V_A := FixedPoints.subgroup A_H V
  let : IsElementaryAbelian 2 V_A := isElementaryAbelian_subgroup V_A
  obtain ⟨P, _hP, _hcore, _hmapcard, hdata, _hmP⟩ :=
    local_recursive_sl2_data h S hS_elem hScard hmin A hAmax hAcard hind
  have hcore3 : IsPGroup 3 (oddCore (H ⧸ A_H)) :=
    (oddCore_isPGroup_three_of_sl2Product
      (G := H ⧸ A_H) (V := V_A) (P : Subgroup (H ⧸ A_H)) hdata.product).1
  have hlocal :=
    local_quotient_oddCore_commutator h (S : Subgroup G) A hS_elem hAmax.1
  have hmap3 : IsPGroup 3
      ((W_A.subgroupOf H).map (QuotientGroup.mk' A_H)) := by
    rw [← hlocal.1]
    exact hcore3
  obtain ⟨n, hn⟩ := hmap3.exists_card_eq
  exact IsPGroup.of_card (p := 3) (n := n) (hlocal.2.1.symm.trans hn)

end Stellmacher.SectionOne.SmallMProof
