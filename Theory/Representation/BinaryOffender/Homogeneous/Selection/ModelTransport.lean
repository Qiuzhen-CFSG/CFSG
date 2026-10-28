module
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.FaithfulSections
public import Theory.Representation.OrthogonalFourPlusMatrix.NormalizerNonFF
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.NonFF
/-!
# Model bounds on repeated alternating-square sections

A section whose restriction to a normal subgroup has a fixed faithful local
model inherits both normal-subgroup faithfulness and the model's non-FF
bound.  The subgroup is marked by two alternating groups of degree five;
the local model is either the natural orthogonal four-space or the tensor
square of the deleted permutation module.  Reindexing the actual subgroup
inclusion transports the equivalence, and normality of its marked range
allows the full-normalizer non-FF results to apply.

The final theorem accepts the literal group-algebra equivalence produced by
the homogeneous two-section selection, supplying the certificate used by
`irreducible_of_faithful_nonFF_sections`.
Source: Aschbacher--Smith D.3.9(1), printed pp.199--200.
-/

public noncomputable section
open scoped MonoidAlgebra
open Subgroup Representation
open BinaryPermutation.FiveTensorSquare
namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A marked local-model equivalence transfers faithfulness on the normal
subgroup and the non-FF property of the whole section image. -/
theorem faithful_nonFF_of_a5_model_equiv
    (N H : Subgroup G) [N.Normal] (hNH : N ≤ H)
    {W E : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) H W) (μ : Representation (ZMod 2) N E)
    (hμ : Function.Injective μ)
    (b : Alt × Alt ≃* N)
    (hmodel : (∃ f : Alt × Alt →* ClassicalOrthogonal.FourPlusMatrix.Binary.G,
      Function.Surjective f ∧ Nonempty (Representation.Equiv (μ.comp b.toMonoidHom)
        (ClassicalOrthogonal.FourPlusMatrix.Binary.action.comp f))) ∨
      Nonempty (Representation.Equiv (μ.comp b.toMonoidHom) deletedAction))
    (e : Representation.Equiv (σ.comp (N.subgroupOf H).subtype)
      (μ.comp (subgroupOfEquivOfLe hNH).toMonoidHom)) :
    Function.Injective (σ.comp (inclusion hNH)) ∧
      ¬ IsFFModule (imageRepresentation σ) := by
  let k := subgroupOfEquivOfLe hNH
  let eN : Representation.Equiv (σ.comp (inclusion hNH)) μ := Representation.Equiv.mk e.toLinearEquiv (by
    intro n
    have he := e.isIntertwining' (k.symm n)
    have hk : (N.subgroupOf H).subtype (k.symm n) = inclusion hNH n := by
      apply Subtype.ext
      exact congrArg (fun z : N => (z : G)) (k.apply_symm_apply n)
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hk,
      show subgroupOfEquivOfLe hNH (k.symm n) = n from k.apply_symm_apply n] using he)
  have hf : Function.Injective (σ.comp (inclusion hNH)) := by
    intro n m hnm
    apply hμ
    ext v
    obtain ⟨w,rfl⟩ := eN.toLinearEquiv.surjective v
    have hn := LinearMap.congr_fun (eN.isIntertwining' n) w
    have hm := LinearMap.congr_fun (eN.isIntertwining' m) w
    change eN.toLinearEquiv ((σ.comp (inclusion hNH)) n w) = μ n (eN.toLinearEquiv w) at hn
    change eN.toLinearEquiv ((σ.comp (inclusion hNH)) m w) = μ m (eN.toLinearEquiv w) at hm
    exact hn.symm.trans ((congrArg eN.toLinearEquiv (LinearMap.congr_fun hnm w)).trans hm)
  refine ⟨hf,?_⟩
  let i : Alt × Alt →* H := (inclusion hNH).comp b.toMonoidHom
  have hir : i.range = N.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact (b y).property
    · intro hx
      obtain ⟨y,hy⟩ := b.surjective ⟨x,hx⟩
      refine ⟨y,?_⟩
      apply Subtype.ext
      exact congrArg (fun z : N => (z : G)) hy
  let : i.range.Normal := hir ▸ inferInstance
  let eb : Representation.Equiv (σ.comp i) (μ.comp b.toMonoidHom) :=
    Representation.Equiv.mk eN.toLinearEquiv (fun g => eN.isIntertwining' (b g))
  rcases hmodel with hmodel | hmodel
  · obtain ⟨f,hf,⟨em⟩⟩ := hmodel
    exact ClassicalOrthogonal.FourPlusMatrix.Binary.image_not_ff_of_marked_normal_range
      σ i f hf (eb.trans em)
  · obtain ⟨em⟩ := hmodel
    exact BinaryPermutation.FiveTensorSquare.image_not_ff_of_marked_normal_range σ i (eb.trans em)


/-- The exact module equivalence supplied by homogeneous section selection
certifies faithfulness and the non-FF bound for the selected section. -/
theorem faithful_nonFF_of_a5_local_type
    (ρ : Representation (ZMod 2) G V) (N H : Subgroup G) [N.Normal] (hNH : N ≤ H)
    (S : Subrepresentation (ρ.comp N.subtype))
    (hSf : Function.Injective S.toRepresentation)
    (hmodel : ∃ b : Alt × Alt ≃* N,
      (∃ f : Alt × Alt →* ClassicalOrthogonal.FourPlusMatrix.Binary.G,
        Function.Surjective f ∧ Nonempty (Representation.Equiv
          (S.toRepresentation.comp b.toMonoidHom)
          (ClassicalOrthogonal.FourPlusMatrix.Binary.action.comp f))) ∨
      Nonempty (Representation.Equiv (S.toRepresentation.comp b.toMonoidHom) deletedAction))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) H W) (X : Subrepresentation σ)
    (he : Nonempty ((X.compActors (N.subgroupOf H).subtype).asSubmodule ≃ₗ[(ZMod 2)[N.subgroupOf H]]
      (S.compActors (subgroupOfEquivOfLe hNH).toMonoidHom).asSubmodule)) :
    Function.Injective (X.toRepresentation.comp (inclusion hNH)) ∧
      ¬ IsFFModule (imageRepresentation X.toRepresentation) := by
  obtain ⟨b,hmodel⟩ := hmodel
  obtain ⟨e⟩ := he
  let er := equiv_of_asSubmodule_equiv (σ.comp (N.subgroupOf H).subtype)
    ((ρ.comp N.subtype).comp (subgroupOfEquivOfLe hNH).toMonoidHom)
    (X.compActors (N.subgroupOf H).subtype)
    (S.compActors (subgroupOfEquivOfLe hNH).toMonoidHom) e
  exact faithful_nonFF_of_a5_model_equiv N H hNH
    X.toRepresentation S.toRepresentation hSf b hmodel er

end Representation.BinaryOffender.Homogeneous
