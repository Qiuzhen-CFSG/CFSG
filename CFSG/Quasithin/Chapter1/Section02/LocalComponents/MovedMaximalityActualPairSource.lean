module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityActualPairOrders
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityActualPairGeometry
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityEvenModels
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityOddModels
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalitySporadicModelsHigmanSims
/-!
# Original moved-component maximality

The complete Theorem C list for the normalized containing quotient is
exhausted. The checked even, odd and earlier sporadic restrictions combine
with the actual-pair order exclusions for J₄/Rudvalis and the Held Sylow
action contradiction. Hence a moved non-PSL₂(4) local component has no
strict containing member of L(G,T). The full KnownSimple predicate and
the original local and movement hypotheses are retained.

Source: Aschbacher--Smith, A.3.12 and 1.2.8(3), pp.47--48 and 506--507.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
variable {G : Type*} [Group G] [Finite G]

/-- The original moving non-A₅ component has no Sylow-normalized containing
local component. All source Theorem C alternatives are discharged. -/
theorem actual_pair_normalized_chain_impossible
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G))
    (hnot : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4) : False := by
  let C := K.subgroupOf (K ⊔ (T : Subgroup G))
  let Q := C ⧸ solvableRadical C
  obtain ⟨hs,_,hmodel,hu⟩ := moved_normalized_remaining_simple_quotient hG T hB hK hBK hTK hm
  let := hs
  let := hK.1.perfect
  rcases hmodel with (ha | ha) | ⟨p,hp,ho,unitary,ho3⟩ | hr | hb | hspor
  · exact hu (alternating_seven_sylow_overgroup_component_unique ha)
  · exact hu (even_sylow_overgroup_component_unique (Or.inr (Or.inr ha)))
  · exact hu (odd_ternary_sylow_overgroup_component_unique hp ho unitary ho3)
  · exact hu (even_sylow_overgroup_component_unique (Or.inl hr))
  · exact hu (even_sylow_overgroup_component_unique (Or.inr (Or.inl hb)))
  · obtain ⟨name,hn,iso⟩ := sporadic_model_remaining_after_higman_sims hspor hu
    let eK : K ≃* C := (subgroupOfEquivOfLe
      (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)).symm
    let eQ : (K ⧸ solvableRadical K) ≃* Q :=
      QuotientGroup.congr _ _ eK (map_solvableRadical_equiv eK)
    rcases hn with rfl | rfl | rfl
    · exact actual_pair_not_janko_four hG T hB hBK hTK hm hnot ⟨eQ.trans iso.some⟩
    · have he : Nonempty ((K ⧸ solvableRadical K) ≃* Held.He) := ⟨eQ.trans iso.some⟩
      exact actual_pair_not_held_of_seven hG T hB hBK hTK hm
        (actual_pair_held_smaller_seven hG T hB hBK hTK hm hnot he) he
    · exact actual_pair_not_rudvalis hG T hB hBK hTK hm hnot ⟨eQ.trans iso.some⟩

/-- Source 1.2.8(3): every original moved non-PSL₂(4) local component is
inclusion-maximal in L(G,T), with the complete KnownSimple hypothesis. -/
theorem moved_local_mem_LStar
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B : Subgroup G} (hB : B ∈ L G (T : Subgroup G))
    (hm : B < conjugateSpanBy B (T : Subgroup G))
    (hnot : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4) :
    B ∈ LStar G (T : Subgroup G) := by
  refine ⟨hB,fun K hK hBK => ?_⟩
  rcases moved_local_chain_eq_or_normalized hG T hB hK hBK hm hnot with he | hn
  · exact he.symm
  · exact (actual_pair_normalized_chain_impossible hG T hB hK hBK hn hm hnot).elim
end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
