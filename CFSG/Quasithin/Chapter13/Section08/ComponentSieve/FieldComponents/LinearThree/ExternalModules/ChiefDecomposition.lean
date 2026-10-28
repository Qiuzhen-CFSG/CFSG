module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.ChiefDecomposition.Alternatives
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.ChiefDecomposition.Sections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.ChiefDecomposition.Product
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.ChiefDecomposition.Pairing
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Chief sections in the external-component branches of 13.8.21(1)

Every component-noncentral chief section in the A₆ configuration restricts
to two Steinberg modules or two natural and two dual modules. In the compatible
SL₃(2) × S₃ configuration it is an external tensor product with the concrete
S₃ augmentation module, retaining natural, dual-natural and Steinberg choices.
All identifications are intertwining equivalences on the literal sections.

A chief section is irreducible, and the cubic norm operator passes the source
commutator-generation identity to that section. The proved irreducible pairing
and product calculations then apply; their H.6.1 input is discharged by the
actual binary catalogue. Perfection supplies a noncentral chief section from
nontrivial component action. The generalized-Fitting product and simplicity
of its factors give section faithfulness without full conjugation image.

The final source adapters use the conjugation action of H/O₂(H) on U_H/V₁
and the marked subgroup images. Compatible structural identifications and
commutator generation remain source inputs; numerical exclusions and the
remaining clauses of 13.8.21 belong to the parent argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.8.21(1), printed pp.956–957; H.6.1, printed p.386.
-/

public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- The A₆-branch decomposition, with the H.6.1 catalogue and all Clifford
multiplicities discharged, on every literal component-noncentral chief section. -/
theorem paired_noncentral_chief_factors [Finite H] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (K X : Subgroup H) [K.Normal] [X.Normal]
    (eK : K ≃* BinaryLinearThree.Group) (hs : PairedStructure K X)
    (hgen : subspaceCommutator ρ ⊤ X = ⊤) :
    PairedNoncentralChiefFactors ρ K eK := by
  intro L N hLN hK
  exact irreducible_paired_alternatives (sectionRepresentation ρ L N) K X eK hs
    (chief_section_irreducible ρ L N hLN)
    (section_generated_of_card_three ρ X hs.card_three hgen L N) hK

private theorem component_simple (K : Subgroup H) (eK : K ≃* BinaryLinearThree.Group) :
    IsSimpleGroup K := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup BinaryLinearThree.Group := Matrix.PSL3Two.equiv.isSimpleGroup
  exact eK.isSimpleGroup

/-- The genuine generalized-Fitting product makes each noncentral chief
section faithful. This applies to both source configurations: no full
automorphism-image assumption is needed. -/
theorem external_chief_section_faithful [Finite H]
    (ρ : Representation (ZMod 2) H U) (K X : Subgroup H) [K.Normal] [X.Normal]
    (eK : K ≃* BinaryLinearThree.Group) (hX : Nat.card X = 3)
    (hc : ∀ k : K, ∀ x : X, Commute (k : H) (x : H))
    (hF : Theory.GroupTheory.generalizedFitting H = K ⊔ X)
    (hgen : subspaceCommutator ρ ⊤ X = ⊤)
    (L N : Subrepresentation ρ) (hLN : L ⋖ N)
    (hK : ∃ k : K, ∃ v, sectionRepresentation ρ L N k v ≠ v) :
    Function.Injective (sectionRepresentation ρ L N) := by
  let : IsSimpleGroup K := component_simple K eK
  exact chief_section_faithful ρ K X
    (joint_centralizer_le_external_of_linearThree K X eK hc hF) hX hgen L N hLN hK

/-- Nontrivial action of the actual SL₃(2) component supplies a noncentral
chief section; perfection is proved for that model and transported through eK. -/
theorem exists_noncentral_chief_section_of_linearThree [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (K : Subgroup H) [K.Normal]
    (eK : K ≃* BinaryLinearThree.Group) (hn : ∃ k : K, ∃ v, ρ k v ≠ v) :
    ∃ L N : Subrepresentation ρ, L ⋖ N ∧
      ∃ k : K, ∃ v, sectionRepresentation ρ L N k v ≠ v := by
  let : Group.IsPerfect BinaryLinearThree.Group := Atlas.sl_perfect 3 (by decide)
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := eK.symm.toMonoidHom) eK.symm.surjective
  exact exists_noncentral_chief_section ρ K hn

/-- Faithfulness of the component action suffices for existence. There is no
assumption that faithfulness automatically passes to arbitrary sections. -/
theorem exists_noncentral_chief_section_of_faithful_component
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (K : Subgroup H) [K.Normal]
    (eK : K ≃* BinaryLinearThree.Group) (hf : Function.Injective (ρ.comp K.subtype)) :
    ∃ L N : Subrepresentation ρ, L ⋖ N ∧
      ∃ k : K, ∃ v, sectionRepresentation ρ L N k v ≠ v := by
  apply exists_noncentral_chief_section_of_linearThree ρ K eK
  let : IsSimpleGroup K := component_simple K eK
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  by_contra! h
  apply hk
  apply hf
  ext v
  simpa using h k v

private theorem marked_cubic_card (eH : H ≃* TensorGroup) (X : Subgroup H)
    (hmark : tensorCubic.map eH.symm.toMonoidHom = X) : Nat.card X = 3 := by
  rw [← hmark, Subgroup.card_map_of_injective eH.symm.injective,
    tensorCubic, Subgroup.card_map_of_injective (fun a b h => congrArg Prod.snd h),
    nat_card_alternatingGroup]
  norm_num

/-- The marked product decomposition with the component catalogue discharged.
The marking also supplies the order of X and finiteness of the acting group. -/
theorem tensor_noncentral_chief_factors_of_marking [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (eH : H ≃* TensorGroup)
    (X : Subgroup H) (hmark : tensorCubic.map eH.symm.toMonoidHom = X)
    (hgen : subspaceCommutator ρ ⊤ X = ⊤) :
    TensorNoncentralChiefFactors ρ eH := by
  let : Finite H := Finite.of_equiv TensorGroup eH.symm.toEquiv
  exact tensor_noncentral_chief_factors ρ eH linearThreeIrreducibleCatalogue
    X (marked_cubic_card eH X hmark) hmark hgen

/-- The product alternatives as equivalences of the original H-chief section.
The component marking converts noncentrality of the literal K-action into
noncentrality of the first product factor. All three model choices remain. -/
theorem tensor_chief_section_alternatives_of_marking [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (eH : H ≃* TensorGroup)
    (K X : Subgroup H) (eK : K ≃* BinaryLinearThree.Group)
    (hKmark : ∀ k : K, eH k = (eK k, 1))
    (hXmark : tensorCubic.map eH.symm.toMonoidHom = X)
    (hgen : subspaceCommutator ρ ⊤ X = ⊤)
    (L N : Subrepresentation ρ) (hLN : L ⋖ N)
    (hn : ∃ k : K, ∃ v, sectionRepresentation ρ L N k v ≠ v) :
    Nonempty ((sectionRepresentation ρ L N).Equiv (naturalTensor.comp eH.toMonoidHom)) ∨
    Nonempty ((sectionRepresentation ρ L N).Equiv (dualNaturalTensor.comp eH.toMonoidHom)) ∨
    Nonempty ((sectionRepresentation ρ L N).Equiv (steinbergTensor.comp eH.toMonoidHom)) := by
  let : Finite H := Finite.of_equiv TensorGroup eH.symm.toEquiv
  apply tensor_chief_section_alternatives ρ eH linearThreeIrreducibleCatalogue
    X (marked_cubic_card eH X hXmark) hXmark hgen L N hLN
  obtain ⟨k, v, hv⟩ := hn
  refine ⟨eK k, v, ?_⟩
  simpa only [← hKmark k, eH.symm_apply_apply] using hv

section SourceAction
open scoped IsMulCommutative
variable {G : Type*} [Group G]
    (H V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
    [FiniteDimensional (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- The paired conclusion for the actual source action. In this branch
X* is L₁*, and K* is the specified image of the component in H/O₂(H). -/
theorem source_paired_noncentral_chief_factors [Finite G] (act : SourceAction H V₃ V₁)
    (K L₁ : Subgroup G) [(Source.starImage H K).Normal] [(Source.starImage H L₁).Normal]
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (hs : PairedStructure (Source.starImage H K) (Source.starImage H L₁))
    (hgen : subspaceCommutator act.representation ⊤ (Source.starImage H L₁) = ⊤) :
    PairedNoncentralChiefFactors act.representation (Source.starImage H K) eK :=
  paired_noncentral_chief_factors act.representation _ _ eK hs hgen

/-- The three product alternatives for the actual source action and marked
component. The natural choice is left to the parent's numerical argument. -/
theorem source_tensor_chief_section_alternatives (act : SourceAction H V₃ V₁)
    (K X : Subgroup G) (eH : Source.Hstar H ≃* TensorGroup)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (hKmark : ∀ k : Source.starImage H K, eH k = (eK k, 1))
    (hXmark : tensorCubic.map eH.symm.toMonoidHom = Source.starImage H X)
    (hgen : subspaceCommutator act.representation ⊤ (Source.starImage H X) = ⊤)
    (L N : Subrepresentation act.representation) (hLN : L ⋖ N)
    (hn : ∃ k : Source.starImage H K, ∃ v,
      sectionRepresentation act.representation L N k v ≠ v) :
    Nonempty ((sectionRepresentation act.representation L N).Equiv
      (naturalTensor.comp eH.toMonoidHom)) ∨
    Nonempty ((sectionRepresentation act.representation L N).Equiv
      (dualNaturalTensor.comp eH.toMonoidHom)) ∨
    Nonempty ((sectionRepresentation act.representation L N).Equiv
      (steinbergTensor.comp eH.toMonoidHom)) :=
  tensor_chief_section_alternatives_of_marking act.representation eH _ _ eK
    hKmark hXmark hgen L N hLN hn

end SourceAction
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
