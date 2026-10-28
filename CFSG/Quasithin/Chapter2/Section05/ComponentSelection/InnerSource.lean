module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ModelClassification
/-! # The original inner mark and component center
The complete marked classifier leaves only inner actions after the genuine
empty-Gamma arguments exclude outer A6 and A7 actions. Odd-core inversion
from the original ambient mark then forces Z(L)=O₂(L). The component need
not be normal in the ambient local group.
Source: Aschbacher--Smith 2.5.2 and Notation 2.5.4, pp.551,554. -/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
theorem MathieuSourceSetup.inner_action
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅) :
    ∃ α : MulAut L, (∀x:L,(α x:G)=z*(x:G)*z⁻¹) ∧ α∈(MulAut.conj (G:=L)).range := by
  let h := c.localSetup hG structural115Input sourceC
  obtain ⟨α,hα,hm⟩ := c.modelAction115_knownSimple hG
  refine ⟨α,hα,?_⟩
  cases hm with
  | lie _ _ hi => exact hi
  | two_cover _ _ _ hi => exact hi
  | six σ hσ ha => exact (alternating_six_action_false c.gamma hempty h α hα σ hσ ha).elim
  | seven σ hσ ha => exact (alternating_seven_action_false c.gamma hempty h α hα σ hσ ha).elim
  | odd _ hi => exact hi
  | sporadic _ _ _ hi => exact hi.1


theorem MathieuSourceSetup.center_eq_twoCore
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅) : center L=pCore 2 L := by
  let h := c.localSetup hG structural115Input sourceC
  let := h.quasisimple
  obtain ⟨α,hα,hi⟩ := MathieuSourceSetup.inner_action c hG sourceC hempty
  apply MulAut.center_eq_twoCore_of_inner_inverts_oddCore α hi
  intro x hx
  let e : L ≃* L.subgroupOf H := (subgroupOfEquivOfLe c.component_le).symm
  have hex : e x∈pPrimeCore 2 (L.subgroupOf H) := by
    rw [← pPrimeCore_map_iso 2 e]
    exact mem_map_of_mem e.toMonoidHom hx
  have hHx : (e x : H)∈pPrimeCore 2 H :=
    c.component.1.pPrimeCore_map_le (mem_map_of_mem (L.subgroupOf H).subtype hex)
  apply Subtype.ext
  rw [hα]
  exact (c.hypotheses115 hG).inverts_oddCore (e x) hHx
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
