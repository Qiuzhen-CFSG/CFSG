module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical.TensorFacts.Coordinates
public import Theory.Representation.GeneralLinearNatural

/-!
# Faithfulness and the absence of tensor transvections

If the S₃ factor is trivial, a moved vector in the first factor yields an
injective displacement map from the augmentation plane. If the S₃ factor is
nontrivial, one of its off-diagonal entries is one. Projection onto that
coordinate makes the displacement map on the three-dimensional first factor
injective. Thus every nonidentity actor has displacement rank at least two.

The only finite check concerns the six permutations on the concrete binary
augmentation plane; it is checked by the Lean kernel. These facts are used
in the tensor branch of Aschbacher–Smith 13.8.21(1), printed p.957.
-/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

@[expose] public section
open Matrix Representation Representation.BinaryOffender TensorProduct
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical.TensorFacts

private noncomputable def tensorLeft (v : BinaryLinearThree.Vector) :
    (Fin 2 → ZMod 2) →ₗ[ZMod 2] TensorSpace :=
  (TensorProduct.mk (ZMod 2) BinaryLinearThree.Vector S3Natural v).comp
    s3Coordinates.symm.toLinearMap

private lemma coordinates_tensorLeft (v : BinaryLinearThree.Vector) (x : Fin 2 → ZMod 2) :
    coordinates (tensorLeft v x) = fun i => v i • x := by
  change coordinates (v ⊗ₜ[ZMod 2] s3Coordinates.symm x) = _
  rw [coordinates_tmul, s3Coordinates.apply_symm_apply]

private lemma tensorLeft_injective (v : BinaryLinearThree.Vector) (hv : v ≠ 0) :
    Function.Injective (tensorLeft v) := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨i,hi⟩ := hex
  intro x y h
  have hh := congrArg (fun z => coordinates z i) h
  rw [coordinates_tensorLeft, coordinates_tensorLeft] at hh
  ext k
  exact mul_left_cancel₀ hi (congrFun hh k)

private lemma tensorLeft_displacement (a : BinaryLinearThree.Group) (v : BinaryLinearThree.Vector)
    (x : Fin 2 → ZMod 2) :
    (naturalTensor (a,1) - 1) (tensorLeft v x) = tensorLeft (BinaryLinearThree.W a v - v) x := by
  change TensorProduct.map (BinaryLinearThree.W a)
    (BinaryPermutation.coreRepresentation (Fin 3) 1)
    (v ⊗ₜ[ZMod 2] s3Coordinates.symm x) - (v ⊗ₜ[ZMod 2] s3Coordinates.symm x) = _
  rw [map_one, TensorProduct.map_tmul, Module.End.one_apply, ← TensorProduct.sub_tmul]
  rfl

private lemma displacement_rank_first (a : BinaryLinearThree.Group) (ha : a ≠ 1) :
    2 ≤ Module.finrank (ZMod 2) (LinearMap.range (naturalTensor (a,1) - 1)) := by
  have hex : ∃ v, BinaryLinearThree.W a v ≠ v := by
    by_contra! h
    apply ha
    apply specialLinearNatural_injective 3
    apply LinearMap.ext
    intro v
    simpa only [map_one, Module.End.one_apply] using h v
  obtain ⟨v,hv⟩ := hex
  let f := (naturalTensor (a,1) - 1).rangeRestrict.comp (tensorLeft v)
  have hf : Function.Injective f := by
    intro x y h
    apply tensorLeft_injective (BinaryLinearThree.W a v - v) (sub_ne_zero.mpr hv)
    have hh := congrArg Subtype.val h
    change (naturalTensor (a,1) - 1) (tensorLeft v x) =
      (naturalTensor (a,1) - 1) (tensorLeft v y) at hh
    simpa only [tensorLeft_displacement] using hh
  simpa using LinearMap.finrank_le_finrank_of_injective hf

private lemma s3_moving_axis (p : Equiv.Perm (Fin 3)) (hp : p ≠ 1) :
    ∃ x : Fin 2 → ZMod 2, ∃ k : Fin 2, x k = 0 ∧ s3Action p x k = 1 := by
  revert p
  decide +kernel

private noncomputable def tensorRight (x : Fin 2 → ZMod 2) :
    BinaryLinearThree.Vector →ₗ[ZMod 2] TensorSpace :=
  (TensorProduct.mk (ZMod 2) BinaryLinearThree.Vector S3Natural).flip (s3Coordinates.symm x)

private lemma coordinates_tensorRight_displacement (g : TensorGroup) (x : Fin 2 → ZMod 2)
    (v : BinaryLinearThree.Vector) (i : Fin 3) (k : Fin 2) :
    coordinates ((naturalTensor g - 1) (tensorRight x v)) i k =
      (BinaryLinearThree.W g.1 v) i * s3Action g.2 x k - v i * x k := by
  change coordinates (TensorProduct.map (BinaryLinearThree.W g.1)
    (BinaryPermutation.coreRepresentation (Fin 3) g.2)
    (v ⊗ₜ[ZMod 2] s3Coordinates.symm x) - (v ⊗ₜ[ZMod 2] s3Coordinates.symm x)) i k = _
  rw [TensorProduct.map_tmul, map_sub, coordinates_tmul, coordinates_tmul,
    s3Coordinates_action, s3Coordinates.apply_symm_apply]
  rfl

private lemma displacement_rank_second (g : TensorGroup) (hg : g.2 ≠ 1) :
    3 ≤ Module.finrank (ZMod 2) (LinearMap.range (naturalTensor g - 1)) := by
  obtain ⟨x,k,hzero,hone⟩ := s3_moving_axis g.2 hg
  let f := (naturalTensor g - 1).rangeRestrict.comp (tensorRight x)
  have hf : Function.Injective f := by
    intro v w h
    apply (BinaryLinearThree.W.apply_bijective g.1).injective
    ext i
    have hh := congrArg (fun z => coordinates z.val i k) h
    change coordinates ((naturalTensor g - 1) (tensorRight x v)) i k =
      coordinates ((naturalTensor g - 1) (tensorRight x w)) i k at hh
    rw [coordinates_tensorRight_displacement, coordinates_tensorRight_displacement] at hh
    simpa only [hzero, hone, mul_zero, mul_one, sub_zero] using hh
  simpa [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector] using
    LinearMap.finrank_le_finrank_of_injective hf

/-- Every nonidentity tensor actor moves a subspace of dimension at least two. -/
theorem displacement_rank_ge_two (g : TensorGroup) (hg : g ≠ 1) :
    2 ≤ Module.finrank (ZMod 2) (LinearMap.range (naturalTensor g - 1)) := by
  rcases g with ⟨a,p⟩
  by_cases hp : p = 1
  · subst p
    exact displacement_rank_first a (fun ha => hg (Prod.ext ha rfl))
  · exact le_trans (by decide) (displacement_rank_second (a,p) hp)

/-- The literal external tensor representation is faithful. -/
theorem naturalTensor_faithful : Function.Injective naturalTensor := by
  apply (MonoidHom.ker_eq_bot_iff naturalTensor).mp
  apply bot_unique
  intro g hg
  apply Subgroup.mem_bot.mpr
  by_contra h
  have hr := displacement_rank_ge_two g h
  have hρ : naturalTensor g = 1 := hg
  have hzero : naturalTensor g - 1 = 0 := by rw [hρ]; exact sub_self (1 : TensorSpace →ₗ[ZMod 2] TensorSpace)
  rw [hzero, LinearMap.range_zero] at hr
  simp at hr

/-- No tensor actor induces a transvection. -/
theorem fixedCodim_zpowers_ne_one (g : TensorGroup) :
    fixedCodim naturalTensor (Subgroup.zpowers g) ≠ 1 := by
  rw [fixedCodim_zpowers_eq_range]
  by_cases hg : g = 1
  · subst g
    have hzero : naturalTensor (1 : TensorGroup) - 1 = 0 := by
      rw [map_one]
      exact sub_self (1 : TensorSpace →ₗ[ZMod 2] TensorSpace)
    rw [hzero, LinearMap.range_zero]
    simp
  · have := displacement_rank_ge_two g hg
    omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical.TensorFacts
