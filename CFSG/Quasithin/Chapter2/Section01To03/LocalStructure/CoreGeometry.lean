module

public import CFSG.Quasithin.Chapter2.Section01To03.Selection
public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import Theory.GroupTheory.PCoreCentralizer

/-!
# Core normalizers and central Sylow geometry in Γ₀

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
2.3.8(5c,6) and 2.3.9(1–4), printed pp.524–525.

Selection transports the actual Sylow subgroup to N_G(O₂(H)). Relative
normality then places C_{O₂(M)}(O₂(H)) in that Sylow subgroup. Characteristic
two in M puts the center of an extending Sylow subgroup in O₂(M), hence in S.
The same centralizer bound gives characteristic two of H ∩ M by 1.1.4(4).
All cores and Sylow centers below are their literal images in G.
-/

public section
namespace CFSG.Quasithin.Chapter2
open Subgroup
variable {G : Type*} [Group G] [Finite G] {M H U L : Subgroup G}

/-- Lemma 2.3.9(1), preserving each of the two starred families separately. -/
theorem lemma_2_3_9_1 (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype) :
    let N := normalizer (twoCore H : Set G)
    N ∈ gammaZero (Chapter1.He G) M ∧
    (∃ P : Sylow 2 N, (P : Subgroup N).map N.subtype = (S : Subgroup H).map H.subtype) ∧
    (∃ P : Sylow 2 ↥(N ⊓ M), (P : Subgroup ↥(N ⊓ M)).map (N ⊓ M).subtype =
      (S : Subgroup H).map H.subtype) ∧
    (H ∈ gammaStar (Chapter1.He G) M → N ∈ gammaStar (Chapter1.He G) M) ∧
    (H ∈ gammaMax (Chapter1.He G) M → N ∈ gammaMax (Chapter1.He G) M) := by
  have hgam : H ∈ gamma (Chapter1.He G) M := hH.elim (fun h => h.1.1) (fun h => h.1)
  have hn := (lemma_2_3_8_3 hgam hpair).2
  exact lemma_2_3_7_2 hH hpair S hUS ⟨hn.1, le_normalizer_twoCore H⟩

/-- Lemma 2.3.9(2): centralization inside O₂(M) forces membership in S. -/
theorem lemma_2_3_9_2 (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype) :
    twoCore M ⊓ centralizer (twoCore H : Set G) ≤ (S : Subgroup H).map H.subtype := by
  have hex₀ := (lemma_2_3_9_1 hH hpair S hUS).2.2.1
  have hex : ∃ P : Sylow 2 ↥(M ⊓ normalizer (twoCore H : Set G)),
      (P : Subgroup ↥(M ⊓ normalizer (twoCore H : Set G))).map
        (M ⊓ normalizer (twoCore H : Set G)).subtype = (S : Subgroup H).map H.subtype := by
    rwa [inf_comm (normalizer (twoCore H : Set G)) M] at hex₀
  obtain ⟨P, hP⟩ := hex
  exact hP ▸ pCoreIn_inf_centralizer_le_sylow M (twoCore H) P

/-- Lemma 2.3.8(5c), including the sharper containment in O₂(H). -/
theorem lemma_2_3_8_5c (hH : H ∈ gammaZero (Chapter1.He G) M)
    (he : H ∈ Chapter1.He G)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    {R : Subgroup G} (hQR : twoCore H ≤ R) :
    twoCore M ⊓ centralizer (R : Set G) ≤ twoCore H ∧
    twoCore M ⊓ centralizer (R : Set G) ≤ R := by
  have hc := lemma_2_3_9_2 hH hpair S hUS
  have hQ : twoCore M ⊓ centralizer (twoCore H : Set G) ≤ twoCore H :=
    fun x hx => he ⟨map_subtype_le _ (hc hx), hx.2⟩
  have hR := (inf_le_inf_left (twoCore M) (centralizer_le hQR)).trans hQ
  exact ⟨hR, hR.trans hQR⟩

/-- The core-centralizer premise of 1.1.5, with the actual intersection core. -/
theorem gammaZero_intersection_core_centralizer (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype) :
    twoCore M ⊓ centralizer (twoCore (H ⊓ M) : Set G) ≤ (S : Subgroup H).map H.subtype := by
  have hSM := (beta_mono hpair.1.1 hUS (S.isPGroup'.map H.subtype)).2.1
  have hQ : twoCore H ≤ twoCore (H ⊓ M) :=
    le_pCoreIn_inf (isPGroup_pCoreIn 2 H) (pCoreIn_le 2 H)
      ((pCoreIn_le_sylow H S).trans hSM) (le_normalizer_twoCore H)
  exact (inf_le_inf_left _ (centralizer_le hQ)).trans (lemma_2_3_9_2 hH hpair S hUS)

/-- Lemma 2.3.9(4), by the characteristic-two inheritance criterion 1.1.4(4). -/
theorem lemma_2_3_9_4 (hM : M ∈ Chapter1.He G)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype) :
    H ⊓ M ∈ Chapter1.He G := by
  have hSb := beta_mono hpair.1.1 hUS (S.isPGroup'.map H.subtype)
  refine Chapter1.lemma_1_1_4_4 (M := M) (N := H ⊓ M) ?_ inf_le_right hM ?_
  · intro he
    exact hSb.1.1 (bot_unique (he ▸ le_inf (map_subtype_le _) hSb.2.1))
  · exact (gammaZero_intersection_core_centralizer hH hpair S hUS).trans
      (le_inf (map_subtype_le _) hSb.2.1)

end CFSG.Quasithin.Chapter2
