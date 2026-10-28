module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.ChiefDecomposition
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors.TensorModels
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical.TensorFacts
/-!
# The covered-A₆ tensor sieve and critical four-group

The binary catalogue and the marked cubic commutator identity give three
external tensor alternatives on every noncentral chief section. An actual
quadratic actor witnessing q ≤ 2 eliminates the Steinberg tensor, leaving
natural and dual-natural tensors under the same product identification.
Nontrivial component action supplies such a chief section.

A natural tensor section is faithful and has no transvections. Fixed
codimension monotonicity then excludes transvections on the original module.
The exact earlier 13.8.18(4) implication forces a critical actor in the marked
point radical to fill that order-four radical.

The natural/dual orientation is deliberately retained. A graph twist exchanges
these modules but also exchanges point and line parabolics; it does not by
itself supply the natural section with the required source marking. The seed
argument and final critical-pair assembly remain separate obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1), covered-A₆ paragraph, printed p.957, using B.4 and 13.8.18(4).
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- The numerical sieve on every literal noncentral chief section. The
single-Steinberg estimate is the precise earlier B.4 input. -/
theorem tensor_chief_section_natural_or_dual
    (ρ : Representation (ZMod 2) H U) (eH : H ≃* TensorGroup)
    (K X : Subgroup H) (eK : K ≃* BinaryLinearThree.Group)
    (hKmark : ∀ k : K, eH k = (eK k, 1))
    (hXmark : tensorCubic.map eH.symm.toMonoidHom = X)
    (hgen : subspaceCommutator ρ ⊤ X = ⊤)
    (hS : ∀ A, IsElementaryTwo A → IsQuadratic BinaryLinearThree.S A →
      rank A < fixedCodim BinaryLinearThree.S A)
    (hsmall : quadraticRatio ρ ≤ 2)
    (L N : Subrepresentation ρ) (hLN : L ⋖ N)
    (hn : ∃ k : K, ∃ v, sectionRepresentation ρ L N k v ≠ v) :
    Nonempty ((sectionRepresentation ρ L N).Equiv (naturalTensor.comp eH.toMonoidHom)) ∨
    Nonempty ((sectionRepresentation ρ L N).Equiv (dualNaturalTensor.comp eH.toMonoidHom)) := by
  let : Finite H := Finite.of_equiv TensorGroup eH.symm.toEquiv
  rcases tensor_chief_section_alternatives_of_marking ρ eH K X eK
    hKmark hXmark hgen L N hLN hn with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · obtain ⟨e⟩ := h
    obtain ⟨A, hA, hq, hc⟩ := (quadraticRatio_le_two_iff ρ).mp hsmall
    have hl := OuterActors.steinberg_tensor_bound_of_equiv
      (sectionRepresentation ρ L N) eH e hS A hA (quadratic_section ρ L N hq)
    have hu := fixedCodim_section_le ρ L N A
    omega

/-- Nontrivial component action supplies a chief section of one of the two
six-dimensional types, with an actual intertwining equivalence. -/
theorem exists_natural_or_dual_tensor_chief_section
    (ρ : Representation (ZMod 2) H U) (eH : H ≃* TensorGroup)
    (K X : Subgroup H) [K.Normal] (eK : K ≃* BinaryLinearThree.Group)
    (hKmark : ∀ k : K, eH k = (eK k, 1))
    (hXmark : tensorCubic.map eH.symm.toMonoidHom = X)
    (hgen : subspaceCommutator ρ ⊤ X = ⊤)
    (hn : ∃ k : K, ∃ v, ρ k v ≠ v)
    (hS : ∀ A, IsElementaryTwo A → IsQuadratic BinaryLinearThree.S A →
      rank A < fixedCodim BinaryLinearThree.S A)
    (hsmall : quadraticRatio ρ ≤ 2) :
    ∃ L N : Subrepresentation ρ, L ⋖ N ∧
      (Nonempty ((sectionRepresentation ρ L N).Equiv (naturalTensor.comp eH.toMonoidHom)) ∨
       Nonempty ((sectionRepresentation ρ L N).Equiv (dualNaturalTensor.comp eH.toMonoidHom))) := by
  obtain ⟨L, N, hLN, hnK⟩ := exists_noncentral_chief_section_of_linearThree ρ K eK hn
  exact ⟨L, N, hLN, tensor_chief_section_natural_or_dual ρ eH K X eK hKmark hXmark
    hgen hS hsmall L N hLN hnK⟩

/-- A natural tensor section excludes transvections on the entire action.
Section faithfulness is proved from the model equivalence before applying
the section inequality; it is not inferred from faithfulness of the whole. -/
theorem natural_tensor_section_no_transvections
    (ρ : Representation (ZMod 2) H U) (eH : H ≃* TensorGroup)
    (L N : Subrepresentation ρ)
    (e : (sectionRepresentation ρ L N).Equiv (naturalTensor.comp eH.toMonoidHom)) :
    ∀ g : H, fixedCodim ρ (Subgroup.zpowers g) ≠ 1 := by
  let σ := sectionRepresentation ρ L N
  have he (g : H) (v) : e.toLinearEquiv (σ g v) = naturalTensor (eH g) (e.toLinearEquiv v) :=
    LinearMap.congr_fun (e.isIntertwining' g) v
  have hf : Function.Injective σ := by
    intro a b hab
    apply eH.injective
    apply MarkedCritical.TensorFacts.naturalTensor_faithful
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
    rw [← he, ← he, hab]
  apply no_transvection_of_faithful_section ρ L N hf
  intro g
  rw [fixedCodim_map_equivariant σ naturalTensor eH.toMonoidHom e.toLinearEquiv he,
    MonoidHom.map_zpowers]
  exact MarkedCritical.TensorFacts.fixedCodim_zpowers_ne_one _

open scoped IsMulCommutative
variable {G : Type*} [Group G]
    (J V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH J V₃)).Normal]
    [IsMulCommutative (Source.Utilde J V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde J V₃ V₁))]
    [FiniteDimensional (ZMod 2) (Additive (Source.Utilde J V₃ V₁))]

/-- The source critical actor fills the point radical. The rank implication
is the explicit earlier 13.8.18(4) input, transported to the chosen conjugate
actor. Its no-transvection premise is discharged using the chief section.
The containment must use the same product marking as that section. -/
theorem source_natural_tensor_critical_image_eq_radical
    (act : SourceAction J V₃ V₁) (eH : Source.Hstar J ≃* TensorGroup)
    (L N : Subrepresentation act.representation)
    (hchief : IsNaturalTensorChiefSection act.representation eH L N)
    (B : Subgroup G)
    (hmark : (Source.starImage J B).map eH.toMonoidHom ≤ MarkedCritical.tensorPointRadical)
    (hlarge : (∀ g : Source.Hstar J,
      fixedCodim act.representation (Subgroup.zpowers g) ≠ 1) →
        1 < rank (Source.starImage J B)) :
    (Source.starImage J B).map eH.toMonoidHom = MarkedCritical.tensorPointRadical := by
  obtain ⟨_, ⟨e⟩⟩ := hchief
  have hr := hlarge (natural_tensor_section_no_transvections act.representation eH L N e)
  let A := (Source.starImage J B).map eH.toMonoidHom
  have hrA : 1 < rank A := by
    rw [rank_map_injective eH.toMonoidHom eH.injective]
    exact hr
  by_contra hn
  have hlt : A < MarkedCritical.tensorPointRadical := lt_of_le_of_ne hmark hn
  have hA0 : A ≠ ⊥ := by
    intro he
    rw [he, Representation.BinaryOffender.rank_bot] at hrA
    omega
  have hc := MarkedCritical.TensorFacts.card_proper_radical A hlt hA0
  change 1 < Nat.log 2 (Nat.card A) at hrA
  rw [hc] at hrA
  norm_num at hrA
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
