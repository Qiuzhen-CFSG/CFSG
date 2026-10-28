module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.Models
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Paired chief factors and actors inside the component

An actor on either paired module pays twice the fixed codimension of one
Steinberg or natural-dual factor. The earlier, strict single-factor bounds
therefore rule out a quadratic ratio at most two for an actor inside K.
The proof transports along the specified component isomorphism and uses an
actual invariant section; neither the actor's rank nor its kernel is discarded.

Consequently, a global ratio bound supplies an actor outside K. Handling that
actor requires the actual outer action, and remains a separate obligation.
In particular these lemmas do not assert the entire A₆-branch exclusion.

Source: Aschbacher–Smith 13.8.21(1), printed p.956, using the earlier module
bounds of B.4 (combined manuscript of 1 March 2004).
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]
  (ρ : Representation (ZMod 2) BinaryLinearThree.Group U)

/-- The arithmetic exclusion on the concrete paired modules. The earlier
inputs concern a single Steinberg module and a single natural-dual pair. -/
theorem paired_module_exclusion
    (hpaired : PairedAlternatives ρ)
    (hS : ∀ A, IsElementaryTwo A → IsQuadratic BinaryLinearThree.S A →
      rank A < fixedCodim BinaryLinearThree.S A)
    (hND : ∀ A, IsElementaryTwo A → IsQuadratic naturalDual A →
      rank A < fixedCodim naturalDual A)
    (A : Subgroup BinaryLinearThree.Group) (hA : IsElementaryTwo A)
    (hq : IsQuadratic ρ A) (hsmall : fixedCodim ρ A ≤ 2 * rank A) : False := by
  have exclude {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
      [FiniteDimensional (ZMod 2) E]
      (σ : Representation (ZMod 2) BinaryLinearThree.Group E)
      (e : ρ.Equiv (σ.prod σ))
      (hσ : IsQuadratic σ A → rank A < fixedCodim σ A) : False := by
    have he (g : BinaryLinearThree.Group) (v : U) :
        e (ρ g v) = (σ.prod σ) g (e v) :=
      LinearMap.congr_fun (e.isIntertwining' g) v
    have hprod := quadratic_of_equivariant_surjection ρ (σ.prod σ)
      e.toLinearMap e.surjective he A hq
    have hcod := fixedCodim_le_of_equivariant_surjection ρ (σ.prod σ)
      e.toLinearMap e.surjective he A
    rw [fixedCodim_prod] at hcod
    have hlt := hσ ((quadratic_prod_iff σ σ A).mp hprod).1
    omega
  unfold PairedAlternatives at hpaired
  rcases hpaired with hs | hn
  · obtain ⟨e⟩ := hs
    exact exclude BinaryLinearThree.S e (hS A hA)
  · obtain ⟨e⟩ := hn
    exact exclude naturalDual e (hND A hA)

variable {H : Type*} [Group H]

/-- A quadratic actor contained in K cannot satisfy the ratio bound when
one actual section has the paired restriction. The condition `A ≤ K` is
essential here; this theorem makes no assertion about outer actors. -/
theorem paired_component_actor_exclusion
    (τ : Representation (ZMod 2) H U) (K : Subgroup H)
    (eK : K ≃* BinaryLinearThree.Group) (L N : Subrepresentation τ)
    (hpaired : PairedAlternatives (componentAction (sectionRepresentation τ L N) K eK))
    (hS : ∀ A, IsElementaryTwo A → IsQuadratic BinaryLinearThree.S A →
      rank A < fixedCodim BinaryLinearThree.S A)
    (hND : ∀ A, IsElementaryTwo A → IsQuadratic naturalDual A →
      rank A < fixedCodim naturalDual A)
    (A : Subgroup H) (hAK : A ≤ K) (hA : IsElementaryTwo A)
    (hq : IsQuadratic τ A) (hsmall : fixedCodim τ A ≤ 2 * rank A) : False := by
  let σ := sectionRepresentation τ L N
  let ι := K.subtype.comp eK.symm.toMonoidHom
  let B := (A.subgroupOf K).map eK.toMonoidHom
  have hmap : B.map ι = A := by
    change ((A.subgroupOf K).map eK.toMonoidHom).map
      (K.subtype.comp eK.symm.toMonoidHom) = A
    rw [Subgroup.map_map]
    have he : (K.subtype.comp eK.symm.toMonoidHom).comp eK.toMonoidHom = K.subtype := by
      ext k
      simp
    rw [he, Subgroup.map_subgroupOf_eq_of_le hAK]
  have hι : Function.Injective ι := K.subtype_injective.comp eK.symm.injective
  have hrank : rank B = rank A := by
    rw [← hmap, rank_map_injective ι hι]
  have helem : IsElementaryTwo B := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : IsElementaryAbelian 2 A := hA.2
    let : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf hAK
    refine ⟨?_, IsElementaryAbelian.map eK.toMonoidHom⟩
    intro hbot
    apply hA.1
    rw [← hmap, hbot, Subgroup.map_bot]
  have hqσ := quadratic_section τ L N hq
  have hqB : IsQuadratic (componentAction σ K eK) B := by
    intro a ha b hb v
    exact hqσ (ι a) (hmap ▸ Subgroup.mem_map_of_mem ι ha)
      (ι b) (hmap ▸ Subgroup.mem_map_of_mem ι hb) v
  have hcod : fixedCodim (componentAction σ K eK) B = fixedCodim σ A := by
    change Module.finrank (ZMod 2) (_ ⧸ fixedSpace (σ.comp ι) B) = _
    rw [fixedSpace_comp_map, hmap]
    rfl
  apply paired_module_exclusion (componentAction σ K eK) hpaired hS hND B helem hqB
  rw [hcod, hrank]
  exact (fixedCodim_section_le τ L N A).trans hsmall

/-- The remaining actor in the A₆ branch must lie outside the component.
This isolates the missing outer-action calculation without assuming it. -/
theorem exists_quadratic_actor_outside_component [Finite H]
    (τ : Representation (ZMod 2) H U) (K : Subgroup H)
    (eK : K ≃* BinaryLinearThree.Group) (L N : Subrepresentation τ)
    (hpaired : PairedAlternatives (componentAction (sectionRepresentation τ L N) K eK))
    (hS : ∀ A, IsElementaryTwo A → IsQuadratic BinaryLinearThree.S A →
      rank A < fixedCodim BinaryLinearThree.S A)
    (hND : ∀ A, IsElementaryTwo A → IsQuadratic naturalDual A →
      rank A < fixedCodim naturalDual A)
    (hsmall : quadraticRatio τ ≤ 2) :
    ∃ A, IsElementaryTwo A ∧ IsQuadratic τ A ∧
      fixedCodim τ A ≤ 2 * rank A ∧ ¬ A ≤ K := by
  obtain ⟨A, hA, hq, hc⟩ := (quadraticRatio_le_two_iff τ).mp hsmall
  exact ⟨A, hA, hq, hc, fun hAK =>
    paired_component_actor_exclusion τ K eK L N hpaired hS hND A hAK hA hq hc⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
