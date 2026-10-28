module

public import Theory.GroupTheory.CComponent.InvolutionCore
public import CFSG.Quasithin.Chapter1.Section02.ComponentDichotomy.Characteristic
public import CFSG.Quasithin.Chapter1.Section02.ComponentDichotomy.OddCore

/-!
# The original component dichotomy for an involution

The residual commutator hypothesis makes z centralize the odd core of H.
Sylow centrality makes it centralize the two-core. If the C-component is not
quasisimple, the Fitting argument puts z in O₂(H), and the characteristic-two
inheritance argument finishes the dichotomy on the original subgroup H.

Source: Aschbacher–Smith 1.2.11, printed p.508. The printed statement does
not explicitly exclude z=1, though its centralizer argument requires a
nonidentity involution. This theorem makes orderOf z=2 explicit, exactly as
required by the original 14.7.68 application. It makes no assertion for z=1.
-/

public section

namespace CFSG.Quasithin.Chapter1
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- Original 1.2.11 for the nonidentity involution used in 14.7.68. -/
theorem lemma_1_2_11_involution
    (hG : IsSimpleQTKE κ G) (T : Sylow 2 G) (H B : Subgroup G) (z : G)
    (hH : H ∈ Chapter1.H G) (hs : IsSylowIn 2 ((T : Subgroup G) ⊓ H) H)
    (hB : B ∈ cComponentsIn H) (hz : orderOf z = 2)
    (hzB : z ∈ B) (hzTH : z ∈ (T : Subgroup G) ⊓ H)
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
  let zB : B.subgroupOf H := ⟨zH,hzB⟩
  have hq' : ¬ IsQuasisimple (B.subgroupOf H) := by
    intro hq'
    let := hq'
    exact hq (IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hB.1))
  have hzB2 : orderOf zB = 2 := by
    rw [← orderOf_coe zB, ← orderOf_coe zH]
    exact hz
  have hc2 : zH ∈ centralizer (pCore 2 H : Set H) := by
    obtain ⟨S,hS⟩ := hs
    have hHT : H.pCoreIn 2 ≤ (T : Subgroup G) :=
      ((pCoreIn_le_sylow H S).trans_eq hS).trans inf_le_left
    intro x hx
    apply Subtype.ext
    exact hzc x (hHT (mem_map_of_mem H.subtype hx))
  have hco : zH ∈ centralizer (pPrimeCore 2 H : Set H) := by
    intro x hx
    apply Subtype.ext
    exact hodd x (mem_map_of_mem H.subtype hx)
  have hm := hB.2.involution_mem_twoCore hq' zB hzB2 hc2 hco
  exact mem_map_of_mem H.subtype hm
end CFSG.Quasithin.Chapter1
