module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.WholeSpace.External.SourceFaithfulness

/-!
# Full marked coordinates on the moved module

The constituent remains on its original carrier U. Its actual actor supplies
an outer automorphism of K through the realized quotient map. Injectivity of
the coordinate homomorphism on the separate module W forces this actor to
have odd first coordinate. The marked A₅ and S₃ then fill the whole product.
Thus no identification of U with W, or of their constituent quotients, is used.

Source: Aschbacher–Smith, B.4.2(5), printed p.86, and the exceptional external
L₂(4) branch of 13.8.20, printed p.954 (1 March 2004 manuscript).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

/-- Full ambient coordinates retaining the original factor equivalence and
both pointwise markings. The carrier can be the literal moved submodule. -/
structure FullCoordinates {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (K : Subgroup D) (s : Equiv.Perm (Fin 3) →* D)
    extends FactorCoordinates ρ K s where
  groupEquiv : D ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)
  equivariant : ∀ d v, moduleEquiv (ρ d v) =
    BinaryPermutation.FiveTensorQuadratic.tensorAction
      (BinaryPermutation.coreRepresentation (Fin 3)) (groupEquiv d) (moduleEquiv v)
  component_apply : ∀ k : K, groupEquiv (k : D) = ((component k).val, 1)
  symmetricThree_apply : ∀ g, groupEquiv (s g) = (1, g)

namespace FactorCoordinates
variable {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
  {ρ : Representation (ZMod 2) D U} {K : Subgroup D} {s : Equiv.Perm (Fin 3) →* D}
  (c : FactorCoordinates ρ K s) [K.Normal]

private theorem inner_of_even_moved_coordinate (hi : Function.Injective c.ambientHom) (d : D)
    (hd : (c.ambientHom d).1 ∈ alternatingGroup (Fin 5)) :
    ∃ k : K, ∀ x : K, d * x * d⁻¹ = (k : D) * x * (k : D)⁻¹ := by
  let k := c.component.symm ⟨(c.ambientHom d).1, hd⟩
  have hk : (c.component k).val = (c.ambientHom d).1 :=
    congrArg Subtype.val (c.component.apply_symm_apply _)
  refine ⟨k, fun x => ?_⟩
  apply hi
  simp only [map_mul, map_inv, c.ambientHom_component]
  apply Prod.ext
  · change (c.ambientHom d).1 * (c.component x).val * (c.ambientHom d).1⁻¹ =
      (c.component k).val * (c.component x).val * (c.component k).val⁻¹
    rw [hk]
  · change (c.ambientHom d).2 * 1 * (c.ambientHom d).2⁻¹ = 1 * 1 * 1⁻¹
    simp only [mul_one, mul_inv_cancel, inv_one]

private theorem odd_mul_odd_inv (a b : Equiv.Perm (Fin 5))
    (ha : a ∉ alternatingGroup (Fin 5)) (hb : b ∉ alternatingGroup (Fin 5)) :
    a * b⁻¹ ∈ alternatingGroup (Fin 5) := by
  have ha' : Equiv.Perm.sign a = -1 :=
    (Int.units_eq_one_or _).resolve_left ha
  have hb' : Equiv.Perm.sign b = -1 :=
    (Int.units_eq_one_or _).resolve_left hb
  simp only [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_inv, ha', hb']
  decide

/-- A group-level outer actor supplies surjectivity independently of the
carrier on which that actor was obtained. -/
theorem ambientHom_surjective_of_outer_actor (hi : Function.Injective c.ambientHom)
    (houter : ∃ d : D, ¬ ∃ k : K, ∀ x : K,
      d * x * d⁻¹ = (k : D) * x * (k : D)⁻¹) :
    Function.Surjective c.ambientHom := by
  obtain ⟨d, hd⟩ := houter
  have hd : (c.ambientHom d).1 ∉ alternatingGroup (Fin 5) :=
    fun heven => hd (c.inner_of_even_moved_coordinate hi d heven)
  rintro ⟨a, b⟩
  by_cases ha : a ∈ alternatingGroup (Fin 5)
  · let k := c.component.symm ⟨a, ha⟩
    have hk : (c.component k).val = a :=
      congrArg Subtype.val (c.component.apply_symm_apply _)
    refine ⟨(k : D) * s b, ?_⟩
    rw [map_mul, c.ambientHom_component, c.ambientHom_symmetricThree, hk]
    simp only [Prod.mk_mul_mk, mul_one, one_mul]
  · let k := c.component.symm ⟨a * (c.ambientHom d).1⁻¹,
      odd_mul_odd_inv a (c.ambientHom d).1 ha hd⟩
    have hk : (c.component k).val = a * (c.ambientHom d).1⁻¹ :=
      congrArg Subtype.val (c.component.apply_symm_apply _)
    refine ⟨(k : D) * d * s ((c.ambientHom d).2⁻¹ * b), ?_⟩
    rw [map_mul, map_mul, c.ambientHom_component, c.ambientHom_symmetricThree, hk]
    apply Prod.ext
    · change a * (c.ambientHom d).1⁻¹ * (c.ambientHom d).1 * 1 = a
      simp only [mul_one, inv_mul_cancel_right]
    · change 1 * (c.ambientHom d).2 * ((c.ambientHom d).2⁻¹ * b) = b
      simp only [one_mul, mul_inv_cancel_left]

/-- Extend the coordinates using the actual constituent on a potentially
different carrier. Only its proved group-level outer-actor conclusion is used. -/
def fullCoordinatesOfRealizedConstituent
    {U₀ E N : Type*} [AddCommGroup U₀] [Module (ZMod 2) U₀]
    [Group E] [AddCommGroup N] [Module (ZMod 2) N]
    {ρ₀ : Representation (ZMod 2) D U₀} {σ : Representation (ZMod 2) E N}
    {J L : Subgroup E}
    (hi : Function.Injective c.ambientHom)
    (r : ConstituentRealization ρ₀ K σ L)
    (e : MarkedActionEquiv σ J L (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5))) : FullCoordinates ρ K s where
  toFactorCoordinates := c
  groupEquiv := MulEquiv.ofBijective c.ambientHom ⟨hi,
    c.ambientHom_surjective_of_outer_actor hi (by
      obtain ⟨g, hg⟩ := r.exists_outer_actor e
      exact ⟨g, hg⟩)⟩
  equivariant := c.ambientHom_intertwines
  component_apply := c.ambientHom_component
  symmetricThree_apply := c.ambientHom_symmetricThree

end FactorCoordinates

namespace FullCoordinates
variable {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
  {ρ : Representation (ZMod 2) D U} {K : Subgroup D} {s : Equiv.Perm (Fin 3) →* D}
  (c : FullCoordinates ρ K s)

/-- The component is the literal marked A₅ × 1. -/
theorem map_component :
    K.map c.groupEquiv.toMonoidHom = (alternatingGroup (Fin 5)).prod ⊥ := by
  ext p
  constructor
  · rintro ⟨d, hd, rfl⟩
    change c.groupEquiv d ∈ _
    rw [c.component_apply ⟨d, hd⟩]
    exact ⟨(c.component ⟨d, hd⟩).property, Subgroup.one_mem _⟩
  · rintro ⟨ha, hb⟩
    let k := c.component.symm ⟨p.1, ha⟩
    refine ⟨k, k.property, ?_⟩
    change c.groupEquiv (k : D) = p
    rw [c.component_apply]
    exact Prod.ext (congrArg Subtype.val (c.component.apply_symm_apply _))
      (Subgroup.mem_bot.mp hb).symm

/-- The cubic marking is retained on the actual subgroup. -/
theorem map_cubic (X : Subgroup D) (hmark : (alternatingGroup (Fin 3)).map s = X) :
    X.map c.groupEquiv.toMonoidHom =
      (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod (alternatingGroup (Fin 3)) := by
  rw [← hmark]
  ext p
  constructor
  · rintro ⟨d, ⟨g, hg, rfl⟩, rfl⟩
    change c.groupEquiv (s g) ∈ _
    rw [c.symmetricThree_apply]
    exact ⟨Subgroup.one_mem _, hg⟩
  · rintro ⟨ha, hb⟩
    refine ⟨s p.2, ⟨p.2, hb, rfl⟩, ?_⟩
    change c.groupEquiv (s p.2) = p
    rw [c.symmetricThree_apply]
    exact Prod.ext (Subgroup.mem_bot.mp ha).symm rfl

include c in
/-- The actual actor subgroup of K embeds in the action, with no passage
from image cardinality to subgroup cardinality without a kernel proof. -/
theorem actor_injective [K.Normal] (A : Subgroup D) (hA : A ≤ K) :
    Function.Injective (ρ.comp A.subtype) :=
  FactorCoordinates.action_injective_on_component_subgroup c.toFactorCoordinates A hA

end FullCoordinates
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction
end
