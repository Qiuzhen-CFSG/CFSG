module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.SuzukiContainment.ReducedPair
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.SuzukiContainment
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder
public import Theory.GroupTheory.PCoreQuotientCoprimeSylowNormalizer
public import GorensteinWalter.PSL2Center

/-!
# The original Borel in an odd-degree linear–Suzuki pair

The outer group of PSL₂(2ⁿ) has order n. For odd n, the original common
two-subgroup therefore acts inner on the linear quotient, so its entire
local Borel normalizes it. The Suzuki side has odd outer group as well.
Together these make the original common Sylow T normal in the full Borel,
and hence T = O₂(B). The reduction in ReducedPair leaves T unchanged and
gives the exact starred-factor formula of DGS Hypothesis B.

This applies to the original odd-degree quotient-centralizer pair in
Aschbacher–Smith 5.1.16–17, pp.639–640. It supplies the reduced hypothesis
for the DGS85 Part II Suzuki analysis; it does not prove T ≤ R or identify
the arbitrary pair with a Ree amalgam.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Odd linear degree puts the whole original local Borel in N_G(S). -/
theorem odd_linear_borel_normalizes [Finite G] (h : HypothesisF11 L S)
    (i : Fin 2) {n : ℕ} (hn : Odd n)
    (he : ClassicalGroup.IsPSL (L i ⧸ pCore 2 (L i)) 2 (2 ^ n)) :
    borel (L i) S ≤ normalizer (S : Set G) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := he
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hz : center (L i ⧸ pCore 2 (L i)) = ⊥ := by
    apply bot_unique
    intro x hx
    have he : e x ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      (centerCongr e ⟨x,hx⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F, mem_bot] at he
    exact mem_bot.mpr (e.injective (he.trans (map_one e).symm))
  have ho : Nat.Coprime 2 (Nat.card (MulAut.Outer (L i ⧸ pCore 2 (L i)))) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv,
      Theory.PSL2.outer_card_eq_field_degree F hcard]
    exact hn.coprime_two_left
  obtain ⟨P, hP⟩ := h.sylow i
  have hc : (S ⊓ L i).subgroupOf (L i) = (P : Subgroup (L i)) := by
    apply map_injective (L i).subtype_injective
    rw [map_subgroupOf_eq_of_le inf_le_right, hP]
  have hb : (normalizer (P : Set (L i))).map (L i).subtype = borel (L i) S := by
    change (normalizer ((P : Subgroup (L i)) : Set (L i))).map (L i).subtype = _
    rw [← hc, ← subgroupOf_normalizer_eq inf_le_right, subgroupOf_map_subtype, inf_comm]
    rfl
  rw [← hb]
  exact pGroup_sylow_normalizer_le_of_coprime_outer S (L i) h.S_isP
    (h.S_normalizes i) hz ho P (hP ▸ inf_le_left)

/-- On the original odd-degree linear--Suzuki pair, the DGS reduction leaves
the entire common Sylow unchanged. This does not assert S ≤ R. -/
theorem odd_linear_suzuki_reducedSylow_eq [Finite G]
    {T : Sylow 2 G} {A R : Subgroup G}
    (h : HypothesisF11 ![A,R] (T : Subgroup G)) {n m : ℕ}
    (hn : Odd n) (he : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 (2 ^ n))
    (hm : 1 ≤ m)
    (e : (R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    reducedSylow ![A,R] (T : Subgroup G) = (T : Subgroup G) := by
  apply le_antisymm (reducedSylow_le h)
  have hA : borel A (T : Subgroup G) ≤ normalizer (T : Set G) :=
    odd_linear_borel_normalizes h 0 hn he
  have hR : borel R (T : Subgroup G) ≤ normalizer (T : Set G) := by
    have hh := sylow_normal_in_borel_join (h.S_normalizes 1) hm e
    exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer le_sup_left).mp hh)
  apply le_pCoreIn_of_normalizes T.isPGroup' le_sup_right
  exact sup_le (sup_le hA hR) (T : Subgroup G).le_normalizer


/-- The actual odd-degree pair satisfies the full reduced-Borel clause of
DGS Hypothesis B with its original Sylow and its original starred factors. -/
theorem odd_linear_suzuki_borel_structure [Finite G]
    {T : Sylow 2 G} {A R : Subgroup G}
    (h : HypothesisF11 ![A,R] (T : Subgroup G)) {n m : ℕ}
    (hn : Odd n) (he : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 (2 ^ n))
    (hm : 1 ≤ m)
    (e : (R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    let pair := ![A,R]
    let B := commonBorel pair (T : Subgroup G)
    twoCore B = (T : Subgroup G) ∧
      ((T : Subgroup G).subgroupOf B).Normal ∧
      B = (starredParabolic pair (T : Subgroup G) 0 ⊓ B) ⊔
        (starredParabolic pair (T : Subgroup G) 1 ⊓ B) ⊔ twoCore B := by
  have hs := odd_linear_suzuki_reducedSylow_eq h hn he hm e
  refine ⟨hs, ?_, ?_⟩
  · have hh := reduced_sylow_normal h
    rw [hs] at hh
    exact hh
  · change commonBorel ![A,R] (T : Subgroup G) = _ ⊔ reducedSylow ![A,R] (T : Subgroup G)
    rw [hs]
    simpa only [hs] using reduced_borel_product h

end CFSG.Quasithin.ChapterF.Source.SuzukiContainment
