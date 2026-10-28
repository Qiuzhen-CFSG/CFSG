module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.SourceGeneration

/-!
# Transport of the ordinary seed commutator

The source identity V₃ = [V₃,X] descends to the binary seed in U_H/V₁:
each conjugation difference is a vector commutator. Taking the inverse
image of its linear span proves the reverse containment without assuming
normality in the ambient group. This supplies the seed input of
Geometry.normal_seed_generation for the actual SourceAction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.7.5(2), printed p.938, and 13.8.21(1), printed p.956.
The earlier group commutator identity remains an explicit input.
-/

@[expose] public section

open Subgroup Representation
open Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction
variable {G : Type*} [Group G]
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- Descend V₃ = [V₃,X] through the actual conjugation quotient. -/
theorem seed_commutator_of_group_commutator (act : SourceAction H V₃ V₁)
    (X : Subgroup G) (hX : X ≤ H) (hgen : ⁅V₃, X⁆ = V₃) :
    subspaceCommutator act.representation (seedSpace H V₃ V₁)
      (Source.starImage H X) = seedSpace H V₃ V₁ := by
  have hnorm : X ≤ normalizer (V₃ : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hgen.le
  have hstable := seedSpace_invariant H V₃ V₁ act X hnorm
  apply le_antisymm
  · apply subspaceCommutator_le_of_invariant
    exact le_subspaceStabilizer act.representation (seedSpace H V₃ V₁) hstable
  · let D := subspaceCommutator act.representation (seedSpace H V₃ V₁)
      (Source.starImage H X)
    let q := QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
    let B : Subgroup (Source.UH H V₃) := {
      carrier := {u | Additive.ofMul (q u) ∈ D}
      one_mem' := by change Additive.ofMul (q 1) ∈ D; simp
      mul_mem' := by
        intro u v hu hv
        change Additive.ofMul (q (u * v)) ∈ D
        simpa only [map_mul, ofMul_mul] using D.add_mem hu hv
      inv_mem' := by
        intro u hu
        change Additive.ofMul (q u⁻¹) ∈ D
        simpa only [map_inv, ofMul_inv] using D.neg_mem hu }
    have hcomm : ⁅X, V₃⁆ ≤ B.map (Source.UH H V₃).subtype := by
      apply commutator_le.mpr
      intro x hx v hv
      let u : Source.UH H V₃ := ⟨v, le_conjugateSpanBy V₃ H hv⟩
      let a : H := ⟨x, hX hx⟩
      have hd : act.representation (QuotientGroup.mk' (pCore 2 H) a)
          (seedVector H V₃ V₁ ⟨v,hv⟩) - seedVector H V₃ V₁ ⟨v,hv⟩ ∈ D :=
        Submodule.subset_span ⟨_, mem_map_of_mem _ hx, _,
          Submodule.subset_span ⟨⟨v,hv⟩,rfl⟩, rfl⟩
      rw [seedVector, act.conjugation] at hd
      refine ⟨conjugateUH H V₃ a u * u⁻¹, ?_, rfl⟩
      change Additive.ofMul (q (conjugateUH H V₃ a u * u⁻¹)) ∈ D
      simpa only [q, u, map_mul, map_inv, ofMul_mul, ofMul_inv,
        sub_eq_add_neg] using hd
    have hVB : V₃ ≤ B.map (Source.UH H V₃).subtype := by
      rw [commutator_comm, hgen] at hcomm
      exact hcomm
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    obtain ⟨u, hu, he⟩ := hVB v.property
    have heu : u = ⟨v.val, le_conjugateSpanBy V₃ H v.property⟩ := Subtype.ext he
    rw [heu] at hu
    exact hu
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction
