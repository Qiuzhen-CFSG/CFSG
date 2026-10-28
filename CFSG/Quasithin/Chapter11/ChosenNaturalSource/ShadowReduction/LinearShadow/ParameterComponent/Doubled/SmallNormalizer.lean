module

public import Theory.Representation.SL3DoubledNaturalOffenders.NormalizerCoverage
public import Theory.Representation.SL3DoubledNaturalOffenders.TensorEstimate.FixedSpace
public import Theory.Representation.SL3DoubledNaturalOffenders.TensorEstimate.ProjectionBounds
public import Theory.Representation.SemilinearInvolutionFixedCard
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Small elementary actors in the full doubled normalizer

A semilinear involution with nontrivial coefficient action has fixed space of
half the full dimension. Below that codimension every actor is field linear.
Its tensor factors are therefore special linear; a nontrivial multiplicity
factor also has fixed codimension at least 3n. Thus an elementary subgroup
of the binary normalizer with fixed codimension below 3n lies in the identical
SL₃ component, in every positive coefficient degree. The dimensions two and
three make the tensor homomorphism faithful without an odd-degree hypothesis.

Source: Aschbacher--Smith, 11.3.6, printed p.772, the reciprocal natural action.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.SL3DoubledNaturalOffenders
open Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
namespace SmallNormalizer
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable [Algebra (ZMod 2) F]

private theorem involution_linear_of_small_fixedCodim {n : ℕ} (hF : Nat.card F = 2^n)
    (A : Subgroup (Ambient F)) (hc : fixedCodim (action F) A < 3*n)
    (b : Ambient F) (hb : b ∈ A) (hbN : b ∈ SL3DoubledNaturalOffenders.normalizer F)
    (hb2 : b^2=1) :
    ∀ (c : F) (v : Space F), (b : Module.End (ZMod 2) (Space F)) (c • v) =
      c • (b : Module.End (ZMod 2) (Space F)) v := by
  obtain ⟨σ,hσ⟩ := normalizer_semilinear b hbN
  have hsq (v : Space F) : (b : Module.End (ZMod 2) (Space F))
      ((b : Module.End (ZMod 2) (Space F)) v) = v :=
    LinearMap.congr_fun (congrArg Units.val hb2) v
  have hσ2 : Function.Involutive σ := by
    intro a
    have he := hsq (a • (fun (_ : Fin 2) (_ : Fin 3) => (1 : F)))
    rw [hσ,hσ,hsq] at he
    simpa only [Pi.smul_apply,smul_eq_mul,mul_one] using congrFun (congrFun he 0) 0
  have hσ1 : σ = RingEquiv.refl F := by
    by_contra hne
    let U := fixedSpace (action F) (zpowers b)
    let f : Space F →+ Space F := (b : Module.End (ZMod 2) (Space F)).toAddMonoidHom
    have he : Nat.card U ^ 2 = Nat.card (Space F) := by
      have hh := SemilinearInvolution.fixed_card_sq σ hσ2 hne f hsq hσ
      have heq : U.toAddSubgroup = f.eqLocus (AddMonoidHom.id _) := by
        ext v
        exact mem_fixedSpace_zpowers_iff (action F) b v
      rwa [← heq] at hh
    have hdim := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U)
    rw [Nat.card_zmod] at hdim
    have hspace := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Space F)
    rw [Nat.card_zmod,finrank_space hF] at hspace
    rw [hdim,hspace,← pow_mul] at he
    have hdim' := Nat.pow_right_injective (by decide : 2 ≤ 2) he
    have hfix := fixedCodim_add_finrank (action F) (zpowers b)
    rw [finrank_space hF] at hfix
    have hle := NaturalTensor.fixedCodim_mono (action F) (zpowers_le.mpr hb)
    change fixedCodim (action F) (zpowers b) + Module.finrank (ZMod 2) U = 6*n at hfix
    omega
  simpa only [hσ1,RingEquiv.refl_apply] using hσ

omit [Finite F] [CharP F 2] in
/-- The coprime factor dimensions make the tensor homomorphism faithful,
including even coefficient degree. -/
theorem tensor_injective : Function.Injective (tensorRepresentation F).asGroupHom := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨g,c⟩ hp
  have hid (v : Space F) (i : Fin 2) :
      g.val.mulVec (multiplicity F c.val v i) = v i :=
    congrFun (LinearMap.congr_fun (congrArg Units.val hp) v) i
  obtain ⟨a,ha,hg,hc⟩ := tensor_identity_scalar_factors g.val c.val hid
  have ha3 : a^3=1 := by simpa [hg,Matrix.det_smul] using g.property
  have ha2 : a^2=1 := by
    have hi : (a⁻¹)^2=1 := by simpa [hc,Matrix.det_smul] using c.property
    rw [inv_pow,inv_eq_one] at hi
    exact hi
  have ha1 : a=1 := by simpa only [pow_succ,ha2,one_mul] using ha3
  change (g,c) = (1,1)
  apply Prod.ext
  · apply Subtype.ext
    change g.val = 1
    simpa only [ha1,one_smul] using hg
  · apply Subtype.ext
    change c.val = 1
    simpa only [ha1,inv_one,one_smul] using hc

/-- Below half the full doubled dimension, every elementary normalizer actor
belongs to the original identical SL₃ component. No parity restriction on n
or bound on the order of the actor is required. -/
theorem elementary_le_component {n : ℕ} (hF : Nat.card F = 2^n)
    (A : Subgroup (Ambient F)) [IsElementaryAbelian 2 A]
    (hAN : A ≤ SL3DoubledNaturalOffenders.normalizer F)
    (hc : fixedCodim (action F) A < 3*n) : A ≤ component F := by
  intro b hb
  have hb2 : b^2=1 := elemPow_eq_one_of_isElementaryAbelian b hb
  obtain ⟨g,c,hf⟩ := normalizer_linear_tensor_factors b (hAN hb)
    (involution_linear_of_small_fixedCodim hF A hc b hb (hAN hb) hb2)
  obtain ⟨⟨g₀,c₀⟩,he⟩ := involution_mem_tensorSubgroup_of_gl_factors b g c hf hb2
  have hpair : (g₀,c₀)^2=1 := tensor_injective
    (by rw [map_pow,he,hb2,map_one])
  have hc2 : c₀^2=1 := congrArg Prod.snd hpair
  by_cases hc1 : c₀=1
  · refine ⟨g₀,?_⟩
    rw [← he,hc1]
    apply Units.ext
    change representation F g₀ = representation F g₀ * multiplicityRepresentation F 1
    rw [map_one,mul_one]
  have hp : IsPGroup 2 (zpowers c₀) := by
    apply IsPGroup.of_card (n := 1)
    simpa only [pow_one] using (Nat.card_zpowers c₀).trans (orderOf_eq_prime hc2 hc1)
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  obtain ⟨s,hs⟩ := MulAction.exists_smul_eq (MultiplicitySL F) P
    (SpecialLinearGroup.upperUnipotentSylow F 2)
  have hm : s*c₀*s⁻¹ ∈ SpecialLinearGroup.upperUnipotent F := by
    have hh := mem_map_of_mem (MulAut.conj s).toMonoidHom (hP (mem_zpowers c₀))
    have hS := congrArg Sylow.toSubgroup hs
    change (P : Subgroup (MultiplicitySL F)).map (MulAut.conj s).toMonoidHom =
      SpecialLinearGroup.upperUnipotent F at hS
    rw [hS] at hh
    exact hh
  obtain ⟨t,ht⟩ := (SpecialLinearGroup.mem_upperUnipotent F _).mp hm
  have ht0 : t≠0 := by
    intro hz
    rw [hz,SpecialLinearGroup.transvection_coeff_zero] at ht
    have he' : (MulAut.conj s) c₀ = (MulAut.conj s) 1 := by simpa using ht.symm
    exact hc1 ((MulAut.conj s).injective he')
  have hlow := fixedCodim_ge_three_mul_of_conjugate_upper hF g₀ s c₀ ht0 ht.symm
    (he.symm ▸ hb)
  exact (not_lt_of_ge hlow hc).elim
end SmallNormalizer
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
