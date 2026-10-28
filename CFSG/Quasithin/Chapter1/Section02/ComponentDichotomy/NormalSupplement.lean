module
public import CFSG.Quasithin.Chapter1.Section02.ComponentDichotomy
public import Theory.GroupTheory.CComponent.SolvableSupplementInvolution

/-!
# The involution dichotomy with a solvable component quotient

For a normal C-component with solvable quotient, a nonquasisimple component
forces the entire layer to vanish. The original residual commutator
hypothesis centralizes the odd core, and Sylow centrality centralizes the
two-core. The central involution is consequently in O₂(H), so the proved
characteristic-two inheritance argument applies. This variant retains
membership of z in H, without requiring z to belong to the C-component.

Source: Aschbacher--Smith 1.2.11 and its use in 14.2.15, pp.508,985.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter1
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}

/-- Original 1.2.11 for a normal C-component with solvable supplement. The
central involution belongs to H; membership in the component is unnecessary. -/
theorem lemma_1_2_11_of_solvable_component_quotient
    (hG : IsSimpleQTKE κ G) (T : Sylow 2 G) (H B : Subgroup G) (z : G)
    (hH : H ∈ Chapter1.H G) (hs : IsSylowIn 2 ((T : Subgroup G) ⊓ H) H)
    (hB : B ∈ cComponentsIn H)
    [(B.subgroupOf H).Normal] [Group.IsSolvable (H ⧸ B.subgroupOf H)]
    (hz : orderOf z = 2) (hzTH : z ∈ (T : Subgroup G) ⊓ H)
    (hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (hcomm : ∃ A : Subgroup G, A ≤ H ∧ IsElementaryAbelian 2 A ∧
      z ∈ ⁅A, (pResidual 2 (H ⊓ normalizer (A : Set G) : Subgroup G)).map
        (H ⊓ normalizer (A : Set G)).subtype⁆)
    (hCT : (T : Subgroup G) ⊓ centralizer (H.pCoreIn 2 : Set G) ≤
      (T : Subgroup G) ⊓ H) : IsQuasisimple B ∨ H ∈ He G := by
  by_cases hq : IsQuasisimple B
  · exact Or.inl hq
  right
  apply he_of_central_involution_in_core T (hG.evenCharacteristic T) H z hs hz ?_ hzc hCT
  obtain ⟨A,hAH,hA,hAz⟩ := hcomm
  let := hA
  have hsqtk : IsStronglyQuasithin H := by
    have hn : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
      H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
    exact (hG.twoLocal_sqtk
      (show IsTwoLocal (normalizer (H.pCoreIn 2 : Set G)) from
        ⟨H.pCoreIn 2,hH,isPGroup_pCoreIn 2 H,rfl⟩)).stronglyQuasithin.of_injective
      (inclusion hn) (inclusion_injective hn)
  have hodd := relative_residual_centralizes_oddCore H A hsqtk hAH hAz
  let zH : H := ⟨z,hzTH.2⟩
  have hq' : ¬ IsQuasisimple (B.subgroupOf H) := by
    intro hh
    let := hh
    exact hq (IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hB.1))
  have hc2 : zH ∈ centralizer (pCore 2 H : Set H) := by
    obtain ⟨P,hP⟩ := hs
    have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) :=
      ((pCoreIn_le_sylow H P).trans_eq hP).trans inf_le_left
    intro x hx
    apply Subtype.ext
    exact hzc x (hQT (mem_map_of_mem H.subtype hx))
  have hco : zH ∈ centralizer (pPrimeCore 2 H : Set H) := by
    intro x hx
    apply Subtype.ext
    exact hodd x (mem_map_of_mem H.subtype hx)
  have hz2 : orderOf zH = 2 := by rwa [←orderOf_coe zH]
  exact mem_map_of_mem H.subtype (involution_mem_twoCore_of_layer_eq_bot
    (hB.2.layer_eq_bot_of_solvable_quotient hq') zH hz2 hc2 hco)
end CFSG.Quasithin.Chapter1
