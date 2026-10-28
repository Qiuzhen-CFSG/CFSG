module
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115.Transport
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.Source

/-! The full earlier model classification on the original Chapter 2 component.
The selected Sylow and central involution construct every marking premise;
the proved universal A/B/C theorem discharges the classification input.
Only the literal component equivalence is used to change ambient subgroups.
Source: Aschbacher--Smith 2.3.9(7), from 1.1.5(3). -/
public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

theorem MathieuSourceSetup.hypotheses115 {C : GroupClass}
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G) :
    Chapter1.Lemma115Hypotheses H S M z := by
  apply lemma_2_3_8_6 hG c.T c.maximal c.sylow_le c.unique c.gamma c.pair S c.base_le
    c.involution (c.center_le c.mem_center)
  · intro s hs
    obtain ⟨a,ha,he⟩ := c.mem_center
    rw [← he]
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨s,c.sylow_lt.le hs⟩)
  · refine ⟨c.T.subtype c.sylow_le,?_⟩
    intro x hx
    have hxT : x ∈ (c.T : Subgroup G) := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le c.sylow_le] using hx
    obtain ⟨a,ha,he⟩ := c.mem_center
    rw [← he]
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨x,hxT⟩)

theorem MathieuSourceSetup.modelAction115_knownSimple
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) :
    ∃ α : MulAut L, (∀ x : L, (α x : G) = z * (x : G) * z⁻¹) ∧
      ModelAction115 L α := by
  obtain ⟨α,hα,hm⟩ := (Chapter1.lemma_1_1_5_three_knownSimple hG H S M z
    (c.hypotheses115 hG) (L.subgroupOf H) c.component).2.2
  let e : L ≃* L.subgroupOf H := (subgroupOfEquivOfLe c.component_le).symm
  refine ⟨MulAut.congr e.symm α,?_,hm.of_mulEquiv e⟩
  intro x
  exact hα (e x)

end CFSG.Quasithin.Chapter2.ComponentRefinement
