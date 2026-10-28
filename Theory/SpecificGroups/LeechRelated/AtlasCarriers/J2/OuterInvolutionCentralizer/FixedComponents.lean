module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCentralizer.LinearComparison
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCores

/-!
# Every J₂ outer fixed component is the actual PSL₃(2)

The proved native representative comparison and exhaustive outer-involution
fusion identify every whole fixed subgroup with Aut(PSL₃(2)). Its actual
ordinary components map onto the inner subgroup, giving literal component
isomorphisms. Transport across an arbitrary ambient model equivalence retains
the marked automorphism and fixed-component map. The precise residual
three-core consumer also has its former comparison premise discharged.

Source: Aschbacher–Smith 2.5.19, pp.561–562, and 16.1.5(8), 16.1.7(g), p.1172.
-/

public noncomputable section
namespace Sporadic.LeechRelated.J2.OuterInvolutionCentralizer
open Subgroup Theory.GroupTheory

/-- Every outer involution of the actual J₂ carrier has the full fixed group
Aut(PSL₃(2)); the representative comparison is fully discharged. -/
theorem outer_fixed_equiv (a : MulAut Carrier) (ha : orderOf a = 2)
    (ho : a ∉ (MulAut.conj : Carrier →* MulAut Carrier).range) :
    Nonempty (a.fixedSubgroup ≃* MulAut Matrix.PSL3Two.PSL) :=
  OuterInvolutionCores.outer_fixed_equiv_of_representative fixedEquivPGL a ha ho

/-- Under any full fixed-group comparison the actual ordinary component maps
to the literal subgroup of inner automorphisms. -/
theorem component_map_eq_inner (a : MulAut Carrier)
    (e : a.fixedSubgroup ≃* MulAut Matrix.PSL3Two.PSL)
    (D : Subgroup a.fixedSubgroup) (hD : IsComponent a.fixedSubgroup D) :
    D.map e.toMonoidHom = MulAut.innerSubgroup Matrix.PSL3Two.PSL := by
  let := Atlas.Comparisons.Exceptional.psl3Two_simple
  exact (hD.map_equiv e).eq_innerSubgroup Matrix.PSL3Two.Automorphisms.center_psl_eq_bot

/-- Every ordinary component of the outer fixed group is the actual PSL₃(2). -/
theorem outer_component_equiv (a : MulAut Carrier) (ha : orderOf a = 2)
    (ho : a ∉ (MulAut.conj : Carrier →* MulAut Carrier).range)
    (D : Subgroup a.fixedSubgroup) (hD : IsComponent a.fixedSubgroup D) :
    Nonempty (D ≃* Matrix.PSL3Two.PSL) := by
  obtain ⟨e⟩ := outer_fixed_equiv a ha ho
  obtain ⟨f⟩ := Matrix.PSL3Two.Automorphisms.component_equiv _ (hD.map_equiv e)
  exact ⟨(e.subgroupMap D).trans f⟩

/-- Model transport preserves the original automorphism and ordinary component. -/
theorem outer_component_equiv_of_equiv {E : Type*} [Group E]
    (e : E ≃* Carrier) (a : MulAut E) (ha : orderOf a = 2)
    (ho : ∀ g : E, a ≠ MulAut.conj g)
    (D : Subgroup a.fixedSubgroup) (hD : IsComponent a.fixedSubgroup D) :
    Nonempty (D ≃* Matrix.PSL3Two.PSL) := by
  let b := MulAut.congr e a
  have hb : orderOf b = 2 := ((MulAut.congr e).orderOf_eq a).trans ha
  have hbo : b ∉ (MulAut.conj : Carrier →* MulAut Carrier).range := by
    rintro ⟨g,hg⟩
    apply ho (e.symm g)
    apply (MulAut.congr e).injective
    rw [MulAut.congr_conj, e.apply_symm_apply]
    exact hg.symm
  let ef := MulAut.fixedSubgroupCongr e a
  obtain ⟨f⟩ := outer_component_equiv b hb hbo (D.map ef.toMonoidHom) (hD.map_equiv ef)
  exact ⟨(ef.subgroupMap D).trans f⟩

/-- The precise three-core criterion now has no representative-model premise. -/
theorem outer_threeCore_eq_bot (a : MulAut Carrier) (ha : orderOf a = 2)
    (ho : a ∉ (MulAut.conj : Carrier →* MulAut Carrier).range)
    (D : Subgroup (MulAut Carrier))
    (hD : D ≤ centralizer ({a} : Set (MulAut Carrier)))
    (hR : MulAut.fixedPerfectResidualInner a ≤ D) : pCore 3 D = ⊥ :=
  OuterInvolutionCores.outer_threeCore_eq_bot_of_representative fixedEquivPGL a ha ho D hD hR
end Sporadic.LeechRelated.J2.OuterInvolutionCentralizer
