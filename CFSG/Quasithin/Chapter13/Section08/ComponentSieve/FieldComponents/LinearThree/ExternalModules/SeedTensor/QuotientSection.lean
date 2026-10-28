module

public import Theory.Representation.PSL3Two.PointTensor.QuotientSection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.ChiefDecomposition.Product

/-!
# A natural chief section in a noncentral point-tensor quotient

Given an explicit surjection from the actual point-permutation tensor, the
image of the point-core tensor is nonzero whenever the component acts
nontrivially. Choose a maximal proper invariant subspace of that image.
The resulting literal chief quotient has an irreducible multiplicity module,
and tensor surjectivity gives a surjection onto that module from the point
core. Its proved simple-head theorem identifies this multiplicity as natural.

The tensor equivalence and the invariant-subspace cover are transported using
the original marked group isomorphism. The explicit surjection remains an
input; constructing it from the source seed belongs to the source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1), covered-A₆ paragraph, printed p.957; point-core structure H.5–H.6.
-/

public section

open Representation Representation.BinaryOffender InvertedCubicTensor
open BinaryLinearThree BinaryLinearThree.FanoDecomposition
open BinaryLinearThree.PointTensor.QuotientSection
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

/-- Every simple quotient of the point-core tensor has the marked natural orientation. -/
theorem pointCoreTensor_simple_quotient [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) TensorGroup U) [IsIrreducible ρ]
    (q : (tensor U₂).IntertwiningMap ρ) (hq : Function.Surjective q) :
    Nonempty (ρ.Equiv naturalTensor) := by
  have hf : fixedSpace (rightAction ρ) (alternatingGroup (Fin 3)) = ⊥ := by
    apply (fixedFree_iff_fixedSpace_eq_bot (rightAction ρ)).mp
    exact fixedFree_of_surjective (rightAction (tensor U₂)) (rightAction ρ)
      q.toLinearMap hq (fun z => LinearMap.congr_fun (q.isIntertwining' (1,cubic)) z) (tensor_fixedFree U₂)
  let : IsIrreducible (productMultiplicity ρ) :=
    productMultiplicity_irreducible ρ hf inferInstance
  obtain ⟨e⟩ := BinaryLinearThree.FanoCoreStructure.pointCore_simple_quotient
    (productMultiplicity ρ) (onMultiplicity U₂ ρ q) (onMultiplicity_surjective U₂ ρ q hq)
  exact ⟨(productTensorRepresentationEquiv ρ hf).symm.trans (tensorWithS3Equiv e)⟩
private theorem exists_lower_cover {H V : Type*} [Group H] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (N : Subrepresentation ρ) (hN : N ≠ ⊥) :
    ∃ L : Subrepresentation ρ, L ⋖ N := by
  classical
  let P : ℕ → Prop := fun d => ∃ L : Subrepresentation ρ,
    L < N ∧ Module.finrank (ZMod 2) L.toSubmodule + d = Module.finrank (ZMod 2) N.toSubmodule
  have hp : ∃ d, P d := ⟨Module.finrank (ZMod 2) N.toSubmodule,
    ⊥, bot_lt_iff_ne_bot.mpr hN, by
      change Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) V) + _ = _
      rw [finrank_bot, zero_add]⟩
  obtain ⟨L,hLN,hd⟩ := Nat.find_spec hp
  refine ⟨L,hLN,?_⟩
  intro M hLM hMN
  have hdim := Submodule.finrank_lt_finrank_of_lt hLM
  have hdim' := Submodule.finrank_lt_finrank_of_lt hMN
  apply Nat.find_min hp (show Module.finrank (ZMod 2) N.toSubmodule -
    Module.finrank (ZMod 2) M.toSubmodule < Nat.find hp by omega)
  exact ⟨M,hMN,by omega⟩

/-- A component-nontrivial quotient of the actual point tensor contains a literal
natural tensor chief section, with the given product identification unchanged. -/
theorem exists_naturalTensorChiefSection_of_pointTensor_surjective
    {H : Type*} [Group H] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (eH : H ≃* TensorGroup)
    (q : BinaryLinearThree.PointTensor.pointTensor.IntertwiningMap
      (ρ.comp eH.symm.toMonoidHom)) (hq : Function.Surjective q)
    (hn : ∃ k : BinaryLinearThree.Group, ∃ v, ρ (eH.symm (k,1)) v ≠ v) :
    ∃ L N : Subrepresentation ρ, IsNaturalTensorChiefSection ρ eH L N := by
  let qc := q.comp coreInclusion
  have hqc : qc ≠ 0 := core_map_ne_zero (ρ.comp eH.symm.toMonoidHom) q hq hn
  let f : Representation.IntertwiningMap ((tensor U₂).comp eH.toMonoidHom) ρ := {
    toLinearMap := qc.toLinearMap
    isIntertwining' h := by
      apply LinearMap.ext
      intro z
      have he := LinearMap.congr_fun (qc.isIntertwining' (eH h)) z
      change qc (tensor U₂ (eH h) z) = ρ h (qc z)
      change qc (tensor U₂ (eH h) z) = ρ (eH.symm (eH h)) (qc z) at he
      simpa only [MulEquiv.symm_apply_apply] using he }
  let N := f.range
  have hN : N ≠ ⊥ := by
    intro hzero
    apply hqc
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    have hz : f z ∈ N := ⟨z,rfl⟩
    rw [hzero] at hz
    exact hz
  obtain ⟨L,hLN⟩ := exists_lower_cover ρ N hN
  let r : (tensor U₂).IntertwiningMap (N.toRepresentation.comp eH.symm.toMonoidHom) := {
    toLinearMap := f.toLinearMap.rangeRestrict
    isIntertwining' g := by
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      exact LinearMap.congr_fun (qc.isIntertwining' g) z }
  let p : Representation.IntertwiningMap (N.toRepresentation.comp eH.symm.toMonoidHom)
      ((sectionRepresentation ρ L N).comp eH.symm.toMonoidHom) := {
    toLinearMap := (sectionLower ρ L N).toSubmodule.mkQ
    isIntertwining' _ := rfl }
  let : IsIrreducible ((sectionRepresentation ρ L N).comp eH.symm.toMonoidHom) :=
    (irreducible_comp_surjective_iff eH.symm.toMonoidHom eH.symm.surjective _).mpr
      (chief_section_irreducible ρ L N hLN)
  obtain ⟨e⟩ := pointCoreTensor_simple_quotient
    ((sectionRepresentation ρ L N).comp eH.symm.toMonoidHom) (p.comp r)
    ((sectionLower ρ L N).toSubmodule.mkQ_surjective.comp f.toLinearMap.surjective_rangeRestrict)
  exact ⟨L,N,hLN,⟨equivOfProductPullback (sectionRepresentation ρ L N) eH naturalTensor e⟩⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
