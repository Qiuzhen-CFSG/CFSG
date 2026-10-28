module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Surjectivity
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# The two marked permutation factors

These are the literal subgroups in the first branch of 13.8.24: the cycle on
{4,5,6}, and O² of the component fixing those three points. The latter uses
the two-residual, not the two-core. Both contain an actual three-cycle, so an
unordered identification of the marked source factors already supplies the
fixed-cycle input to the module-selection reduction.

The identification itself remains an obligation; `MarkedFactors` only states
its exact contract. The natural seed subsequently distinguishes its order.

Source: Aschbacher–Smith, 13.8.24, printed pp.958–959
(combined manuscript, 1 March 2004).
-/

@[expose] public section
open Equiv Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection

/-- The component fixing the three-point block pointwise. -/
def fourPointComponent : Subgroup S7 :=
  alternatingGroup (Fin 7) ⊓ fixingSubgroup S7 ({4, 5, 6} : Set (Fin 7))

/-- The ambient image of the source's O²(K_{5,6,7}). -/
def fourResidualFactor : Subgroup S7 :=
  (pResidual 2 fourPointComponent).map fourPointComponent.subtype

/-- The source's cyclic factor on its three-point block. -/
def threeFactor : Subgroup S7 := zpowers cycle456

/-- The unordered source marking, stated through the fixed action map. -/
def MarkedFactors {J : Type*} [Group J] (φ : J →* S7) (L₀ X : Subgroup J) : Prop :=
  (L₀.map φ = threeFactor ∧ X.map φ = fourResidualFactor) ∨
  (L₀.map φ = fourResidualFactor ∧ X.map φ = threeFactor)

theorem cycle012_isThreeCycle : Equiv.Perm.IsThreeCycle cycle012 := by
  rw [← card_support_eq_three_iff]
  decide +kernel
theorem cycle456_isThreeCycle : Equiv.Perm.IsThreeCycle cycle456 := by
  rw [← card_support_eq_three_iff]
  decide +kernel

/-- Odd order places this cycle in the intrinsic two-residual. -/
theorem cycle012_mem_fourResidualFactor : cycle012 ∈ fourResidualFactor := by
  have hx : cycle012 ∈ fourPointComponent := by
    refine ⟨cycle012_isThreeCycle.mem_alternatingGroup, ?_⟩
    apply (mem_fixingSubgroup_iff S7).mpr
    intro i hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl | rfl <;> decide +kernel
  refine ⟨⟨cycle012, hx⟩, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  rw [← orderOf_coe, cycle012_isThreeCycle.orderOf]
  decide

/-- The unordered residual marking supplies a three-cycle in L₀*. No
surjectivity or chosen four-dimensional representation is used here. -/
theorem MarkedFactors.exists_threeCycle {J : Type*} [Group J]
    {φ : J →* S7} {L₀ X : Subgroup J} (h : MarkedFactors φ L₀ X) :
    ∃ g ∈ L₀, Equiv.Perm.IsThreeCycle (φ g) := by
  rcases h with ⟨h₀, _⟩ | ⟨h₀, _⟩
  · have hc : cycle456 ∈ L₀.map φ := h₀.symm ▸ mem_zpowers cycle456
    obtain ⟨g, hg, he⟩ := hc
    exact ⟨g, hg, he.symm ▸ cycle456_isThreeCycle⟩
  · have hc : cycle012 ∈ L₀.map φ := h₀.symm ▸ cycle012_mem_fourResidualFactor
    obtain ⟨g, hg, he⟩ := hc
    exact ⟨g, hg, he.symm ▸ cycle012_isThreeCycle⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection
