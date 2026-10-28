module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.FullActionInputs

/-!
# Full marked action from the five-by-three tensor coordinates

Normality of the component places each transported ambient action in the
normalizer of the tensor A₅ action. The proved tensor normalizer calculation
gives a unique pair of coordinate permutations; uniqueness makes these pairs
multiplicative, and faithfulness makes the resulting homomorphism injective.

The marked B.4.2(5) constituent supplies a transposition through the actual
surjection from its ambient actor. Its outer action on K forces an odd first
coordinate. Together with the already marked A₅ and S₃ this fills S₅ × S₃.
The original module equivalence and both pointwise markings are preserved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2(5),
printed p.86, and the external L₂ case of 13.8.20, printed p.954.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.GroupTheory
open scoped TensorProduct
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

namespace FactorCoordinates

variable {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
  {ρ : Representation (ZMod 2) D U} {K : Subgroup D} {s : Equiv.Perm (Fin 3) →* D}
  (c : FactorCoordinates ρ K s)

private abbrev tensorAction :=
  BinaryPermutation.ThreeTensor.action (BinaryPermutation.coreRepresentation (Fin 5))

private theorem tensorAction_eq :
    BinaryPermutation.FiveTensorQuadratic.tensorAction
      (BinaryPermutation.coreRepresentation (Fin 3)) = tensorAction := rfl

private theorem component_intertwines (k : K) (v : U) :
    c.moduleEquiv (ρ k v) = tensorAction ((c.component k).val, 1) (c.moduleEquiv v) := by
  simpa only [map_one, mul_one, tensorAction_eq] using c.intertwines k 1 v

private theorem symmetricThree_intertwines (g : Equiv.Perm (Fin 3)) (v : U) :
    c.moduleEquiv (ρ (s g) v) = tensorAction (1, g) (c.moduleEquiv v) := by
  simpa only [map_one, Subgroup.coe_one, one_mul, tensorAction_eq] using c.intertwines 1 g v

private def transported (d : D) :=
  c.moduleEquiv.symm.trans
    ((LinearEquiv.ofBijective (ρ d) (ρ.apply_bijective d)).trans c.moduleEquiv)

private theorem transported_apply (d : D) (v : U) :
    c.transported d (c.moduleEquiv v) = c.moduleEquiv (ρ d v) := by
  simp only [transported, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.ofBijective_apply]

variable [K.Normal]

private theorem exists_coordinates (d : D) :
    ∃ p : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3),
      ∀ v, c.moduleEquiv (ρ d v) = tensorAction p (c.moduleEquiv v) := by
  let φ : MulAut (alternatingGroup (Fin 5)) :=
    c.component.symm.trans ((MulAut.conjNormal d).trans c.component)
  obtain ⟨p, hp⟩ := BinaryPermutation.FiveTensorNormalizer.tensor_normalizer
    (c.transported d) φ (by
      intro a z
      obtain ⟨k, rfl⟩ := c.component.surjective a
      obtain ⟨v, rfl⟩ := c.moduleEquiv.surjective z
      rw [← c.component_intertwines, c.transported_apply, c.transported_apply]
      have hφ : φ (c.component k) = c.component (MulAut.conjNormal d k) := by
        simp only [φ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [hφ, ← c.component_intertwines]
      congr 1
      simp only [MulAut.conjNormal_apply, ← Module.End.mul_apply, ← map_mul,
        mul_assoc, inv_mul_cancel, mul_one])
  exact ⟨p, fun v => (c.transported_apply d v).symm.trans (hp (c.moduleEquiv v))⟩

private def coordinates (d : D) : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3) :=
  (c.exists_coordinates d).choose

private theorem coordinates_intertwines (d : D) (v : U) :
    c.moduleEquiv (ρ d v) = tensorAction (c.coordinates d) (c.moduleEquiv v) :=
  (c.exists_coordinates d).choose_spec v

/-- The tensor coordinates extend canonically to a homomorphism on the ambient group. -/
def ambientHom : D →* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3) where
  toFun := c.coordinates
  map_one' := by
    apply BinaryPermutation.FiveTensorNormalizer.tensor_coordinates_unique
    intro z
    obtain ⟨v, rfl⟩ := c.moduleEquiv.surjective z
    rw [← c.coordinates_intertwines]
    simp only [map_one, Module.End.one_apply]
  map_mul' d e := by
    apply BinaryPermutation.FiveTensorNormalizer.tensor_coordinates_unique
    intro z
    obtain ⟨v, rfl⟩ := c.moduleEquiv.surjective z
    rw [← c.coordinates_intertwines, map_mul, Module.End.mul_apply,
      c.coordinates_intertwines, c.coordinates_intertwines]
    rw [map_mul]
    rfl

/-- Every ambient element acts through the original, unchanged module coordinates. -/
theorem ambientHom_intertwines (d : D) (v : U) :
    c.moduleEquiv (ρ d v) =
      BinaryPermutation.FiveTensorQuadratic.tensorAction
        (BinaryPermutation.coreRepresentation (Fin 3))
        (c.ambientHom d) (c.moduleEquiv v) := by
  rw [tensorAction_eq]
  exact c.coordinates_intertwines d v

/-- The component marking is retained pointwise. -/
theorem ambientHom_component (k : K) :
    c.ambientHom (k : D) = ((c.component k).val, 1) := by
  apply BinaryPermutation.FiveTensorNormalizer.tensor_coordinates_unique
  intro z
  obtain ⟨v, rfl⟩ := c.moduleEquiv.surjective z
  exact (c.coordinates_intertwines k v).symm.trans (c.component_intertwines k v)

/-- The specified S₃ marking is retained pointwise. -/
theorem ambientHom_symmetricThree (g : Equiv.Perm (Fin 3)) :
    c.ambientHom (s g) = (1, g) := by
  apply BinaryPermutation.FiveTensorNormalizer.tensor_coordinates_unique
  intro z
  obtain ⟨v, rfl⟩ := c.moduleEquiv.surjective z
  exact (c.coordinates_intertwines (s g) v).symm.trans
    (c.symmetricThree_intertwines g v)

/-- Faithfulness of the original action makes the extended homomorphism injective. -/
theorem ambientHom_injective (hρ : Function.Injective ρ) :
    Function.Injective c.ambientHom := by
  intro d e hde
  apply hρ
  ext v
  apply c.moduleEquiv.injective
  rw [c.ambientHom_intertwines, c.ambientHom_intertwines, hde]

private theorem inner_of_even_coordinate (hρ : Function.Injective ρ) (d : D)
    (hd : (c.ambientHom d).1 ∈ alternatingGroup (Fin 5)) :
    ∃ k : K, ∀ x : K, d * x * d⁻¹ = (k : D) * x * (k : D)⁻¹ := by
  let k := c.component.symm ⟨(c.ambientHom d).1, hd⟩
  have hk : (c.component k).val = (c.ambientHom d).1 :=
    congrArg Subtype.val (c.component.apply_symm_apply _)
  refine ⟨k, fun x => ?_⟩
  apply c.ambientHom_injective hρ
  simp only [map_mul, map_inv, c.ambientHom_component]
  apply Prod.ext
  · change (c.ambientHom d).1 * (c.component x).val * (c.ambientHom d).1⁻¹ =
      (c.component k).val * (c.component x).val * (c.component k).val⁻¹
    rw [hk]
  · change (c.ambientHom d).2 * 1 * (c.ambientHom d).2⁻¹ = 1 * 1 * 1⁻¹
    simp only [mul_one, mul_inv_cancel, inv_one]

variable {E N : Type*} [Group E] [AddCommGroup N] [Module (ZMod 2) N]
  {σ : Representation (ZMod 2) E N} {J L : Subgroup E}

/-- Surjectivity of the realized constituent map supplies an odd ambient coordinate. -/
theorem exists_odd_coordinate (hρ : Function.Injective ρ)
    (r : ConstituentRealization ρ K σ L)
    (e : MarkedActionEquiv σ J L (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5))) :
    ∃ d : D, (c.ambientHom d).1 ∉ alternatingGroup (Fin 5) := by
  obtain ⟨g, hg⟩ := r.exists_outer_actor e
  exact ⟨g, fun heven => hg (c.inner_of_even_coordinate hρ g heven)⟩

private theorem odd_mul_odd_inv (a b : Equiv.Perm (Fin 5))
    (ha : a ∉ alternatingGroup (Fin 5)) (hb : b ∉ alternatingGroup (Fin 5)) :
    a * b⁻¹ ∈ alternatingGroup (Fin 5) := by
  have ha' : Equiv.Perm.sign a = -1 :=
    (Int.units_eq_one_or _).resolve_left ha
  have hb' : Equiv.Perm.sign b = -1 :=
    (Int.units_eq_one_or _).resolve_left hb
  simp only [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_inv, ha', hb']
  decide

/-- The marked A₅ and S₃ together with the realized odd actor fill the whole product. -/
theorem ambientHom_surjective (hρ : Function.Injective ρ)
    (r : ConstituentRealization ρ K σ L)
    (e : MarkedActionEquiv σ J L (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5))) :
    Function.Surjective c.ambientHom := by
  obtain ⟨d, hd⟩ := c.exists_odd_coordinate hρ r e
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

/-- Full marked ambient product action. Faithfulness of the constituent is
retained explicitly, as in the source application. -/
def fullActionEquiv (hρ : Function.Injective ρ) (_hσ : Function.Injective σ)
    (r : ConstituentRealization ρ K σ (generalizedFitting E))
    (e : MarkedActionEquiv σ (offenderSubgroup σ) (generalizedFitting E)
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) :
    D ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective c.ambientHom
    ⟨c.ambientHom_injective hρ, c.ambientHom_surjective hρ r e⟩

variable (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
  (r : ConstituentRealization ρ K σ (generalizedFitting E))
  (e : MarkedActionEquiv σ (offenderSubgroup σ) (generalizedFitting E)
    (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))

/-- Full equivariance uses exactly the module equivalence originally supplied in c. -/
theorem fullActionEquiv_intertwines (d : D) (v : U) :
    c.moduleEquiv (ρ d v) =
      BinaryPermutation.FiveTensorQuadratic.tensorAction
        (BinaryPermutation.coreRepresentation (Fin 3))
        (c.fullActionEquiv hρ hσ r e d) (c.moduleEquiv v) :=
  c.ambientHom_intertwines d v

/-- Pointwise marking of the actual component in the full equivalence. -/
theorem fullActionEquiv_component (k : K) :
    c.fullActionEquiv hρ hσ r e (k : D) = ((c.component k).val, 1) :=
  c.ambientHom_component k

/-- Pointwise marking of the actual commuting three-letter subgroup. -/
theorem fullActionEquiv_symmetricThree (g : Equiv.Perm (Fin 3)) :
    c.fullActionEquiv hρ hσ r e (s g) = (1, g) :=
  c.ambientHom_symmetricThree g

/-- The literal component has image A₅ × 1. -/
theorem fullActionEquiv_map_component :
    K.map (c.fullActionEquiv hρ hσ r e).toMonoidHom =
      (alternatingGroup (Fin 5)).prod ⊥ := by
  ext p
  constructor
  · rintro ⟨d, hd, rfl⟩
    change c.fullActionEquiv hρ hσ r e d ∈ _
    rw [c.fullActionEquiv_component hρ hσ r e ⟨d, hd⟩]
    exact ⟨(c.component ⟨d, hd⟩).property, Subgroup.one_mem _⟩
  · rintro ⟨ha, hb⟩
    let k := c.component.symm ⟨p.1, ha⟩
    refine ⟨k, k.property, ?_⟩
    change c.fullActionEquiv hρ hσ r e (k : D) = p
    rw [c.fullActionEquiv_component]
    exact Prod.ext (congrArg Subtype.val (c.component.apply_symm_apply _))
      (Subgroup.mem_bot.mp hb).symm

/-- The specified cubic subgroup has image 1 × A₃. -/
theorem fullActionEquiv_map_cubic :
    ((alternatingGroup (Fin 3)).map s).map (c.fullActionEquiv hρ hσ r e).toMonoidHom =
      (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod (alternatingGroup (Fin 3)) := by
  ext p
  constructor
  · rintro ⟨d, ⟨g, hg, rfl⟩, rfl⟩
    change c.fullActionEquiv hρ hσ r e (s g) ∈ _
    rw [c.fullActionEquiv_symmetricThree]
    exact ⟨Subgroup.one_mem _, hg⟩
  · rintro ⟨ha, hb⟩
    refine ⟨s p.2, ⟨p.2, hb, rfl⟩, ?_⟩
    change c.fullActionEquiv hρ hσ r e (s p.2) = p
    rw [c.fullActionEquiv_symmetricThree]
    exact Prod.ext (Subgroup.mem_bot.mp ha).symm rfl

end FactorCoordinates
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

end
