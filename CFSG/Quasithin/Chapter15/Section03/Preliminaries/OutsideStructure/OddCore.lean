module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.CharacteristicTwo

/-!
# The final odd-core reduction in the outside-overgroup argument

An odd normal subgroup contained in a characteristic-two subgroup is trivial.
Apply this inside I after A.1.26(1) puts O(I) in the centralizer of V or V₂,
and (2) or (3) puts that centralizer in M ∩ I.

The centralization still requires the rank-two action theorem A.1.26(1).
This module does not assume characteristic two for I, nor infer trivial
odd core solely from characteristic two of M ∩ I.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11(8), p.1124; A.1.26(1), pp.25–26.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure
variable {G : Type*} [Group G] [Finite G]

/-- An odd normal subgroup contained in a subgroup with trivial odd core is trivial. -/
theorem oddCore_eq_bot_of_le (H : Subgroup G)
    (hH : pPrimeCore 2 H = ⊥) (hO : pPrimeCore 2 G ≤ H) : pPrimeCore 2 G = ⊥ := by
  let K := (pPrimeCore 2 G).subgroupOf H
  have hK : K = ⊥ := (pPrimeCore_eq_bot_iff (p := 2) (G := H)).mp hH K
    inferInstance (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hO).toEquiv]
      exact pPrimeCore_coprime_card)
  have hm := congrArg (Subgroup.map H.subtype) hK
  rwa [map_subgroupOf_eq_of_le hO, Subgroup.map_bot] at hm

/-- The final odd-core step of (8). Its centralizer premise is supplied by
A.1.26(1) on V or V₂, not by characteristic two of M ∩ I alone. -/
theorem oddCore_eq_bot_of_centralizing (M I W : Subgroup G)
    (hMI : centralizer (pCore 2 ↥(M ⊓ I) : Set ↥(M ⊓ I)) ≤ pCore 2 ↥(M ⊓ I))
    (hc : (pPrimeCore 2 I).map I.subtype ≤ centralizer (W : Set G))
    (hcontrol : I ⊓ centralizer (W : Set G) ≤ M) : pPrimeCore 2 I = ⊥ := by
  have hMcore : pPrimeCore 2 (M.subgroupOf I) = ⊥ := by
    apply Theory.GroupTheory.pPrimeCore_eq_bot_of_centralizer_pCore_le 2
    have heq : (M ⊓ I).subgroupOf I = M.subgroupOf I := inf_subgroupOf_right M I
    rw [← heq]
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      (subgroupOfEquivOfLe (show M ⊓ I ≤ I from inf_le_right))).mpr hMI
  apply oddCore_eq_bot_of_le (M.subgroupOf I) hMcore
  intro x hx
  exact hcontrol ⟨x.property, hc (mem_map_of_mem I.subtype hx)⟩

/-- The H-family condition places I in a maximal two-local, so quasithinness
of G supplies all odd-prime rank bounds needed by A.1.26(1). -/
theorem outside_stronglyQuasithin (hG : IsQuasithin G)
    (Yplus S M I : Subgroup G) (hI : I ∈ outsideFamily Yplus S M) :
    IsStronglyQuasithin I := by
  have hcore : pCore 2 I ≠ ⊥ := by
    intro he
    apply hI.1.1
    change (pCore 2 I).map I.subtype = ⊥
    rw [he, Subgroup.map_bot]
  obtain ⟨N, hN, hIN⟩ := Theory.GroupTheory.exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot I hcore
  exact ((isQuasithin_iff_twoLocal.mp hG) N hN.1).of_injective
    (inclusion hIN) (inclusion_injective hIN)

/-- In particular each odd prime core has rank at most two. -/
theorem outside_odd_core_rank (hG : IsQuasithin G)
    (Yplus S M I : Subgroup G) (hI : I ∈ outsideFamily Yplus S M)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) : primeRank p (pCore p I) ≤ 2 :=
  ((outside_stronglyQuasithin hG Yplus S M I hI).subgroup (pCore p I)) p hp ho


end CFSG.Quasithin.Chapter15.Section03.OutsideStructure

end
