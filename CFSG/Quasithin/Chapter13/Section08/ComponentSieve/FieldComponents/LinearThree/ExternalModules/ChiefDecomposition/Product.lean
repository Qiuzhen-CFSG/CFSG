module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.ChiefDecomposition.Alternatives
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.ChiefDecomposition.Sections
public import Theory.Representation.InvertedCubicTensor
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The three product-chief-module alternatives

For a binary action of SL₃(2) × S₃, the inverted-cubic construction identifies
the module with the tensor product of its transposition-fixed multiplicity
space and the concrete S₃ augmentation module. If the full action is
irreducible, tensoring a proper component-invariant subspace would contradict
irreducibility. Thus the multiplicity space is irreducible and noncentral.
The explicit earlier H.6.1 catalogue identifies it as natural, dual-natural,
or Steinberg; tensoring those actual equivalences gives the three alternatives.

The final theorems apply this construction to the literal chief sections and
transport back through the same marked group isomorphism. No pairing, tensor
decomposition, or dimension-only classification is assumed. Absolute
irreducibility fields of the catalogue are not needed in this product branch.

Source: Aschbacher–Smith 13.8.21(1), printed p.957, combined manuscript of
1 March 2004; H.6.1 supplies the earlier component-module classification.
-/

@[expose] public section

open Representation Representation.BinaryOffender TensorProduct InvertedCubicTensor
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
universe u
variable {U : Type u} [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) TensorGroup U)

/-- The existing inverted-cubic construction as an intertwining equivalence. -/
noncomputable def productTensorRepresentationEquiv
    (h : fixedSpace (rightAction ρ) (alternatingGroup (Fin 3)) = ⊥) :
    (tensorWithS3 (productMultiplicity ρ)).Equiv ρ :=
  .mk (productTensorEquiv ρ h) (fun g => LinearMap.ext (productTensorEquiv_equivariant ρ h g))

/-- A simple product module has simple multiplicity module. A proper invariant
subspace of the multiplicity space would tensor to a proper invariant subspace. -/
theorem productMultiplicity_irreducible [FiniteDimensional (ZMod 2) U]
    (h : fixedSpace (rightAction ρ) (alternatingGroup (Fin 3)) = ⊥)
    (hi : IsIrreducible ρ) : IsIrreducible (productMultiplicity ρ) := by
  let : IsIrreducible ρ := hi
  let : Nontrivial U := Subrepresentation.irreducible_module_nontrivial ρ
  let I := multiplicitySpace (rightAction ρ)
  have hdim := (productPairEquiv ρ h).finrank_eq
  rw [Module.finrank_prod] at hdim
  change Module.finrank (ZMod 2) I + Module.finrank (ZMod 2) I =
    Module.finrank (ZMod 2) U at hdim
  have hpos := Module.finrank_pos (R := ZMod 2) (M := U)
  let : Nontrivial I := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, ?_⟩
  intro S
  let inc : Representation.IntertwiningMap
      (S.toRepresentation.comp (MonoidHom.fst BinaryLinearThree.Group S₃))
      ((productMultiplicity ρ).comp (MonoidHom.fst BinaryLinearThree.Group S₃)) :=
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  let f := (productTensorRepresentationEquiv ρ h).toIntertwiningMap.comp
    (inc.tensor (IntertwiningMap.id
      ((BinaryPermutation.coreRepresentation (Fin 3)).comp (MonoidHom.snd BinaryLinearThree.Group S₃))))
  have hf : Function.Injective f.toLinearMap :=
    (productTensorEquiv ρ h).injective.comp
      (TensorProduct.map_injective_of_flat_flat _ _ S.toSubmodule.subtype_injective
        (Function.injective_id))
  have hd := LinearMap.finrank_range_of_inj hf
  rw [Module.finrank_tensorProduct, natural_finrank] at hd
  change Module.finrank (ZMod 2) (LinearMap.range f.toLinearMap) =
    Module.finrank (ZMod 2) S.toSubmodule * 2 at hd
  rcases eq_bot_or_eq_top f.range with hb | ht
  · left
    have hr : LinearMap.range f.toLinearMap = ⊥ := congrArg Subrepresentation.toSubmodule hb
    rw [hr, finrank_bot] at hd
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.finrank_eq_zero.mp
    change Module.finrank (ZMod 2) S.toSubmodule = 0
    omega
  · right
    have hr : LinearMap.range f.toLinearMap = ⊤ := congrArg Subrepresentation.toSubmodule ht
    rw [hr, finrank_top] at hd
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.eq_top_of_finrank_eq
    change Module.finrank (ZMod 2) S.toSubmodule = Module.finrank (ZMod 2) I
    omega

/-- A noncentral component action survives on the multiplicity module. -/
theorem productMultiplicity_noncentral
    (h : fixedSpace (rightAction ρ) (alternatingGroup (Fin 3)) = ⊥)
    (hn : ∃ k : BinaryLinearThree.Group, ∃ v, ρ (k, 1) v ≠ v) :
    ∃ k v, productMultiplicity ρ k v ≠ v := by
  by_contra! hfix
  obtain ⟨k, v, hv⟩ := hn
  obtain ⟨p, rfl⟩ := (productPairEquiv ρ h).surjective v
  apply hv
  rw [← productPairEquiv_equivariant, hfix, hfix]

/-- Tensoring an intertwining equivalence preserves all action data. -/
noncomputable def tensorWithS3Equiv {V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) BinaryLinearThree.Group V}
    {τ : Representation (ZMod 2) BinaryLinearThree.Group W} (e : σ.Equiv τ) :
    (tensorWithS3 σ).Equiv (tensorWithS3 τ) :=
  .mk (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl (ZMod 2) S3Natural)) (by
    intro g
    ext v w
    change e (σ g.1 v) ⊗ₜ[ZMod 2] (BinaryPermutation.coreRepresentation (Fin 3) g.2 w) =
      τ g.1 (e v) ⊗ₜ[ZMod 2] (BinaryPermutation.coreRepresentation (Fin 3) g.2 w)
    have he : e (σ g.1 v) = τ g.1 (e v) := LinearMap.congr_fun (e.isIntertwining' g.1) v
    rw [he])

/-- The three genuine external-tensor alternatives for an irreducible product
action, before any quadratic-ratio exclusions. -/
theorem irreducible_product_tensor_alternatives [FiniteDimensional (ZMod 2) U]
    (hc : LinearThreeIrreducibleCatalogue.{u})
    (h : fixedSpace (rightAction ρ) (alternatingGroup (Fin 3)) = ⊥)
    (hi : IsIrreducible ρ)
    (hn : ∃ k : BinaryLinearThree.Group, ∃ v, ρ (k, 1) v ≠ v) :
    TensorAlternatives ρ := by
  have halts := hc.classify ↥(multiplicitySpace (rightAction ρ)) (productMultiplicity ρ)
    (productMultiplicity_irreducible ρ h hi) (productMultiplicity_noncentral ρ h hn)
  rcases halts with he | he | he
  · obtain ⟨e⟩ := he
    exact Or.inl ⟨(productTensorRepresentationEquiv ρ h).symm.trans (tensorWithS3Equiv e)⟩
  · obtain ⟨e⟩ := he
    exact Or.inr (Or.inl ⟨(productTensorRepresentationEquiv ρ h).symm.trans
      (tensorWithS3Equiv e)⟩)
  · obtain ⟨e⟩ := he
    exact Or.inr (Or.inr ⟨(productTensorRepresentationEquiv ρ h).symm.trans
      (tensorWithS3Equiv e)⟩)

/-- The marked cubic subgroup in the second direct factor. -/
def tensorCubic : Subgroup TensorGroup :=
  (alternatingGroup (Fin 3)).map (MonoidHom.inr BinaryLinearThree.Group S₃)

variable {H : Type*} [Group H]

/-- The product-branch decomposition on every literal noncentral chief section.
The marked X and the group equivalence are required to be compatible. -/
theorem tensor_noncentral_chief_factors [FiniteDimensional (ZMod 2) U]
    (τ : Representation (ZMod 2) H U) (eH : H ≃* TensorGroup)
    (hc : LinearThreeIrreducibleCatalogue.{u})
    (X : Subgroup H) [Finite X] (hX : Nat.card X = 3)
    (hmark : tensorCubic.map eH.symm.toMonoidHom = X)
    (hgen : subspaceCommutator τ ⊤ X = ⊤) :
    TensorNoncentralChiefFactors τ eH := by
  intro L N hLN hn
  let σ := (sectionRepresentation τ L N).comp eH.symm.toMonoidHom
  have hi : IsIrreducible σ :=
    (irreducible_comp_surjective_iff eH.symm.toMonoidHom eH.symm.surjective _).mpr
      (chief_section_irreducible τ L N hLN)
  have hf : fixedSpace (rightAction σ) (alternatingGroup (Fin 3)) = ⊥ := by
    change fixedSpace (σ.comp (MonoidHom.inr BinaryLinearThree.Group S₃)) _ = ⊥
    rw [fixedSpace_comp_map]
    change fixedSpace ((sectionRepresentation τ L N).comp eH.symm.toMonoidHom) tensorCubic = ⊥
    rw [fixedSpace_comp_map, hmark]
    exact section_fixedSpace_eq_bot_of_card_three τ X hX hgen L N
  exact irreducible_product_tensor_alternatives σ hc hf hi hn

/-- Unpulling an equivalence uses the same group isomorphism on both actions. -/
noncomputable def equivOfProductPullback {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) H U) (eH : H ≃* TensorGroup)
    (π : Representation (ZMod 2) TensorGroup V)
    (e : Representation.Equiv (τ.comp eH.symm.toMonoidHom) π) :
    τ.Equiv (π.comp eH.toMonoidHom) :=
  .mk e.toLinearEquiv (by
    intro h
    ext v
    change e (τ h v) = π (eH h) (e v)
    have he : e (τ (eH.symm (eH h)) v) = π (eH h) (e v) :=
      LinearMap.congr_fun (e.isIntertwining' (eH h)) v
    simpa only [MulEquiv.symm_apply_apply] using he)

/-- The three intertwining equivalences, stated directly on the original
H-chief section for consumers of the numerical exclusions. -/
theorem tensor_chief_section_alternatives [FiniteDimensional (ZMod 2) U]
    (τ : Representation (ZMod 2) H U) (eH : H ≃* TensorGroup)
    (hc : LinearThreeIrreducibleCatalogue.{u})
    (X : Subgroup H) [Finite X] (hX : Nat.card X = 3)
    (hmark : tensorCubic.map eH.symm.toMonoidHom = X)
    (hgen : subspaceCommutator τ ⊤ X = ⊤)
    (L N : Subrepresentation τ) (hLN : L ⋖ N)
    (hn : ∃ k : BinaryLinearThree.Group, ∃ v,
      sectionRepresentation τ L N (eH.symm (k, 1)) v ≠ v) :
    Nonempty ((sectionRepresentation τ L N).Equiv (naturalTensor.comp eH.toMonoidHom)) ∨
    Nonempty ((sectionRepresentation τ L N).Equiv (dualNaturalTensor.comp eH.toMonoidHom)) ∨
    Nonempty ((sectionRepresentation τ L N).Equiv (steinbergTensor.comp eH.toMonoidHom)) := by
  rcases tensor_noncentral_chief_factors τ eH hc X hX hmark hgen L N hLN hn with
    he | he | he
  · obtain ⟨e⟩ := he
    exact Or.inl ⟨equivOfProductPullback (sectionRepresentation τ L N) eH naturalTensor e⟩
  · obtain ⟨e⟩ := he
    refine Or.inr (Or.inl ⟨?_⟩)
    refine .mk e.toLinearEquiv ?_
    intro h
    ext v
    change e (sectionRepresentation τ L N h v) = dualNaturalTensor (eH h) (e v)
    have he : e (sectionRepresentation τ L N (eH.symm (eH h)) v) =
        dualNaturalTensor (eH h) (e v) := LinearMap.congr_fun (e.isIntertwining' (eH h)) v
    simpa only [MulEquiv.symm_apply_apply] using he
  · obtain ⟨e⟩ := he
    exact Or.inr (Or.inr ⟨equivOfProductPullback (sectionRepresentation τ L N) eH steinbergTensor e⟩)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules