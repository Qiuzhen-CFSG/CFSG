module

public import Theory.GroupTheory.PGroup.RankTwoCoreHallExclusion
public import Theory.GroupTheory.PGroup.RankTwoExtraspecial
public import Theory.GroupTheory.PGroup.RankTwoSymplecticType

/-!
# Nontrivial Hall factors in a rank-two solvable core

In a finite solvable odd-core-free group of elementary rank at least three,
assume the two-core has elementary rank two and no elementary four is normal
in the ambient group. If every characteristic abelian subgroup of the core
is cyclic, Hall's decomposition has a nontrivial extraspecial factor.

The pure Hall-factor exclusion rules out the trivial factor. The elementary
rank bound descends through the embedded factors, so the extraspecial factor
is dihedral or quaternion of order eight, or the internal central product
of quaternion and dihedral subgroups of order eight; its order is at most
thirty-two. Both factors are normal in the core, with no assertion of
normality in the ambient solvable group.

Sources: GLS2, Chapter C, Theorem 10.3, Propositions 10.4–10.6 and Lemma 10.11.
-/

open Subgroup

/-- The rank-two quotient core has a genuine extraspecial factor with its
explicit small model, commuting with a Hall factor and generating the core. -/
public theorem exists_rankTwoExtraspecial_hall_factors_pCore
    {K : Type*} [Group K] [Finite K]
    (hsolv : Group.IsSolvable K) (hodd : pPrimeCore 2 K = ⊥)
    (A : Subgroup K) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (V : Subgroup K) [IsElementaryAbelian 2 V]
    (hV : V ≤ pCore 2 K) (hVcard : Nat.card V = 4)
    (hno : ∀ U : Subgroup K, U.Normal → IsElementaryAbelian 2 U → Nat.card U ≠ 4)
    (hrank : ∀ U : Subgroup K, IsElementaryAbelian 2 U → U ≤ pCore 2 K →
      Nat.card U < 8)
    (hchar : ∀ B : Subgroup (pCore 2 K), B.Characteristic →
      IsMulCommutative B → IsCyclic B) :
    ∃ E D : Subgroup (pCore 2 K), E.Normal ∧ D.Normal ∧
      IsExtraspecial 2 E ∧ IsRankTwoExtraspecialModel E ∧ Nat.card E ≤ 32 ∧
      IsBinaryHallFactor D ∧ D ≤ centralizer (E : Set (pCore 2 K)) ∧
      E ⊔ D = ⊤ := by
  have hnot := not_isBinaryHallFactor_pCore_of_elementary_rank_three
    hsolv hodd A hA V hV hVcard hno
  obtain ⟨E, D, hEn, hDn, hE, hD, hc, hgen⟩ :=
    IsPGroup.exists_normal_binaryHallFactors (pCore_isPGroup (p := 2) (G := K)) hchar
  have he : IsExtraspecial 2 E := by
    rcases hE with hE | hE
    · have hDt : D = ⊤ := by simpa only [hE, bot_sup_eq] using hgen
      exact (hnot (hD.of_mulEquiv
        ((MulEquiv.subgroupCongr hDt).trans Subgroup.topEquiv))).elim
    · exact hE
  let : IsExtraspecial 2 E := he
  have hrankQ (U : Subgroup (pCore 2 K)) (hU : IsElementaryAbelian 2 U) :
      Nat.card U < 8 := by
    let : IsElementaryAbelian 2 U := hU
    have h := hrank (U.map (pCore 2 K).subtype) (IsElementaryAbelian.map _)
      (map_subtype_le _)
    simpa only [card_map_of_injective (pCore 2 K).subtype_injective] using h
  have hrankE (U : Subgroup E) (hU : IsElementaryAbelian 2 U) : Nat.card U < 8 := by
    let : IsElementaryAbelian 2 U := hU
    have h := hrankQ (U.map E.subtype) (IsElementaryAbelian.map _)
    simpa only [card_map_of_injective E.subtype_injective] using h
  have hmodel : IsRankTwoExtraspecialModel E := IsExtraspecial.rank_two_classification hrankE
  exact ⟨E, D, hEn, hDn, he, hmodel, hmodel.card_le, hD, hc, hgen⟩
