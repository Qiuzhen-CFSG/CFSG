module
public import Theory.Representation.PSL3Two.IrreducibleCatalogue
public import Theory.Representation.PSL3Two.ResidualFFForms.ConstituentBudget.InvolutionBound
public import Theory.Representation.PSL3Two.SteinbergStructure.ParabolicFactors.CubicFixed
public import Theory.Representation.BinaryOffender.ThreeConjugateNormalizer
public import Theory.Representation.BinaryPrimeDisplacement
public import Theory.SpecificGroups.PSL3Two.ElementOrders
public import Theory.Representation.TensorInvolutionDisplacement
public import Theory.Representation.QuadraticFourGroup.TensorClassification.ExternalTensor
public import Theory.Representation.BinaryTensorThree.ConstituentStability
public import Theory.Representation.BinaryOffender.CubicRatio

/-!
# Excluding the binary Steinberg square under a cubic budget

Every nonidentity element of SL₃(2) moves at least three dimensions on its
Steinberg module: involution generation, the actual cubic fixed-space calculation
and the order-seven binary degree cover all element orders. Hence a nontrivial
single-factor actor moves at least 24 dimensions on the Steinberg square.

For a faithful normal extension, Schur's lemma embeds every elementary actor in
Aut(SL₃(2) × SL₃(2)), whose two-rank is at most four. A cubic ratio at most two
would give a nonidentity involution moving at most eight dimensions. Its induced
automorphism either preserves the factors or exchanges them; in both cases a
commutator moves at least 24 dimensions, contradicting the upper bound of sixteen.
The proof includes outer factor automorphisms and uses the full action kernel.

This excludes the Steinberg catalogue alternative in the binary case of
Aschbacher--Smith D.3.7, printed pp.197--199, as applied in original 3.2.6(2),
printed p.581 (combined manuscript, 1 March 2004).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.NaturalTensor
open Representation.QuadraticFourGroup.TensorClassification
open scoped TensorProduct
namespace BinaryLinearThree.SteinbergSquare
local instance : IsSimpleGroup Group := Atlas.Comparisons.Exceptional.sl3Two_simple

private theorem involution_displacement (a : Group) (ha : a ^ 2 = 1) (hne : a ≠ 1) :
    3 ≤ operatorFixedCodim (S a) := by
  let := IrreducibleCatalogue.steinberg_absolute
  let := IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible S
  have hb := ResidualFFForms.ConstituentBudget.finrank_le_three_mul_involution_fixedCodim S
    (subspaceCommutator_top_eq_top_of_faithful_irreducible S steinberg_injective inferInstance)
    a ha hne
  rw [finrank_steinberg,fixedCodim_zpowers_eq_displacement_rank] at hb
  change 8 ≤ 3 * operatorFixedCodim (S a) at hb
  omega

private theorem element_displacement (a : Group) (hne : a ≠ 1) :
    3 ≤ operatorFixedCodim (S a) := by
  rcases Matrix.PSL3Two.pow_three_or_four_or_seven a with h3 | h4 | h7
  · have hc : Nat.card (zpowers a) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime h3 hne
    have hf := SteinbergStructure.ParabolicFactors.finrank_fixedSpace_order_three (zpowers a) hc
    have hd := fixedCodim_add_finrank S (zpowers a)
    rw [finrank_steinberg,hf,fixedCodim_zpowers_eq_displacement_rank] at hd
    change operatorFixedCodim (S a) + 2 = 8 at hd
    omega
  · by_cases ha : a ^ 2 = 1
    · exact involution_displacement a ha hne
    · have hb := involution_displacement (a ^ 2) (by rw [←pow_mul]; exact h4) ha
      have hm := operatorFixedCodim_le_fixedCodim S (zpowers a) (pow_mem (mem_zpowers a) 2)
      rw [fixedCodim_zpowers_eq_displacement_rank] at hm
      exact hb.trans hm
  · let : Fact (Nat.Prime 7) := ⟨by decide⟩
    have hb := prime_order_le_fixedCodim S steinberg_injective (by decide : Nat.Prime 7)
      (by decide) a (orderOf_eq_prime h7 hne)
    rw [show orderOf (2 : ZMod 7) = 3 from orderOf_eq_prime (by decide) (by decide),fixedCodim_zpowers_eq_displacement_rank] at hb
    exact hb

private theorem rTensor_displacement (A : Module.End (ZMod 2) Steinberg) :
    operatorFixedCodim (A.rTensor Steinberg) = 8 * operatorFixedCodim A := by
  have hd : A.rTensor Steinberg - 1 = (A - 1).rTensor Steinberg := by ext x y; simp
  rw [operatorFixedCodim,hd,LinearMap.rTensor_range]
  rw [LinearMap.finrank_range_of_inj
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)]
  rw [Module.finrank_tensorProduct,finrank_steinberg]
  exact Nat.mul_comm _ _

private theorem lTensor_displacement (A : Module.End (ZMod 2) Steinberg) :
    operatorFixedCodim (A.lTensor Steinberg) = 8 * operatorFixedCodim A := by
  have hd : A.lTensor Steinberg - 1 = (A - 1).lTensor Steinberg := by ext x y; simp
  rw [operatorFixedCodim,hd,LinearMap.lTensor_range]
  rw [LinearMap.finrank_range_of_inj
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)]
  rw [Module.finrank_tensorProduct,finrank_steinberg]
  rfl

private theorem first_displacement (a : Group) (hne : a ≠ 1) :
    24 ≤ operatorFixedCodim (externalTensor S S (a,1)) := by
  change 24 ≤ operatorFixedCodim (TensorProduct.map (S a) (S 1))
  rw [map_one]
  change 24 ≤ operatorFixedCodim ((S a).rTensor Steinberg)
  rw [rTensor_displacement]
  exact Nat.mul_le_mul_left 8 (element_displacement a hne)

private theorem second_displacement (a : Group) (hne : a ≠ 1) :
    24 ≤ operatorFixedCodim (externalTensor S S (1,a)) := by
  change 24 ≤ operatorFixedCodim (TensorProduct.map (S 1) (S a))
  rw [map_one]
  change 24 ≤ operatorFixedCodim ((S a).lTensor Steinberg)
  rw [lTensor_displacement]
  exact Nat.mul_le_mul_left 8 (element_displacement a hne)

private theorem pair_displacement (a b : Group) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hne : a ≠ 1) : 24 ≤ operatorFixedCodim (externalTensor S S (a,b)) := by
  have ha' : S a * S a = 1 := by rw [←map_mul,←pow_two,ha,map_one]
  have hb' : S b * S b = 1 := by rw [←map_mul,←pow_two,hb,map_one]
  have hr := involution_displacement a ha hne
  have hsmall := TensorInvolutionDisplacement.twice_displacement_le (S a) ha'
  have he := TensorInvolutionDisplacement.tensor_displacement_formula (S a) (S b) ha' hb'
  rw [finrank_steinberg] at he hsmall
  change 24 ≤ operatorFixedCodim (TensorProduct.map (S a) (S b))
  nlinarith


/-- The actual Steinberg square cannot have a faithful normal extension with
cubic ratio at most two. All normalizer involutions, including factor exchanges
and graph automorphisms, are covered. -/
theorem not_cubic_normal_extension
    {H V : Type*} [_root_.Group H] [Finite H]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (hf : Function.Injective ρ)
    (i : (Group × Group) →* H) (hi : Function.Injective i) [i.range.Normal]
    (hirr : Representation.IsIrreducible (ρ.comp i))
    (e : Representation.Equiv (ρ.comp i) (externalTensor S S)) (hc : cubicRatio ρ ≤ 2) : False := by
  let N := i.range
  let b : (Group × Group) ≃* N := MonoidHom.ofInjective hi
  let : Representation.IsIrreducible (ρ.comp N.subtype) :=
    (irreducible_comp_surjective_iff i.rangeRestrict i.rangeRestrict_surjective
      (ρ.comp N.subtype)).mp hirr
  obtain ⟨A,hA,_,hbudget⟩ := (cubicRatio_le_nat_iff ρ 2).mp hc
  let : IsElementaryAbelian 2 A := hA.2
  have hAC : A ⊓ centralizer (N : Set H) = ⊥ := by
    apply bot_unique
    intro a ha
    exact BinaryIrreducibleCentralizer.centralizing_square_one_eq_one ρ N hf
      (elemPow_eq_one_of_isElementaryAbelian a ha.1) ha.2
  let c : Group ≃* BinaryTensorThree.Factor := Matrix.PSL3Two.equivGL.trans
    ((Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := ZMod 2)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) BinaryTensorThree.Natural))
  have hr := BinaryTensorThree.rank_le_four_of_faithful_on_tensor_base N A hA hAC
    (b.symm.trans (c.prodCongr c))
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have hbudgeta : fixedCodim ρ (zpowers a) ≤ 8 :=
    (fixedCodim_mono ρ (zpowers_le.mpr ha)).trans (hbudget.trans (by omega))
  let α : MulAut (Group × Group) := (MulAut.congr b.symm) (MulAut.conjNormal a)
  have hconj (g : Group × Group) : i (α g) = a * i g * a⁻¹ :=
    congrArg Subtype.val (b.apply_symm_apply (MulAut.conjNormal a (b g)))
  have hα : α ≠ 1 := by
    intro hz
    apply ha1
    apply BinaryIrreducibleCentralizer.centralizing_square_one_eq_one ρ N hf ha2
    apply mem_centralizer_iff.mpr
    rintro _ ⟨g,rfl⟩
    have hh := hconj g
    rw [hz] at hh
    change i g = a * i g * a⁻¹ at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  have hd (g : Group × Group) :
      operatorFixedCodim (ρ (i g)) = operatorFixedCodim (externalTensor S S g) :=
    operatorFixedCodim_eq_of_equiv _ _ e.toLinearEquiv
      (fun v => LinearMap.congr_fun (e.isIntertwining' g) v)
  have hcomm (g : Group × Group) :
      operatorFixedCodim (externalTensor S S (α g * g⁻¹)) ≤
        2 * fixedCodim ρ (zpowers a) := by
    have hh := fixedCodim_commutator_le_twice ρ a (i g)
    have he : a * i g * a⁻¹ * (i g)⁻¹ = i (α g * g⁻¹) := by
      rw [←hconj,←map_inv,←map_mul]
    rw [he,fixedCodim_zpowers_eq_displacement_rank] at hh
    change operatorFixedCodim (ρ (i (α g * g⁻¹))) ≤ _ at hh
    rwa [hd] at hh
  rcases AutomorphismSquare.normal_form Matrix.PSL3Two.center_eq_bot α with
    ⟨u,v,huv⟩ | ⟨u,v,huv⟩
  · have hne : (∃ x, u x ≠ x) ∨ (∃ x, v x ≠ x) := by
      by_contra! hz
      apply hα
      rw [huv]
      apply MulEquiv.ext
      intro g
      exact Prod.ext (hz.1 g.1) (hz.2 g.2)
    rcases hne with ⟨x,hx⟩ | ⟨x,hx⟩
    · have hb := first_displacement (u x * x⁻¹) (fun he => hx (eq_of_mul_inv_eq_one he))
      have hh := hcomm (x,1)
      have he : α (x,1) * (x,1)⁻¹ = (u x * x⁻¹,1) := by
        rw [huv]
        change (u x * x⁻¹,v 1 * 1⁻¹) = _
        rw [map_one,inv_one,mul_one]
      rw [he] at hh
      omega
    · have hb := second_displacement (v x * x⁻¹) (fun he => hx (eq_of_mul_inv_eq_one he))
      have hh := hcomm (1,x)
      have he : α (1,x) * (1,x)⁻¹ = (1,v x * x⁻¹) := by
        rw [huv]
        change (u 1 * 1⁻¹,v x * x⁻¹) = _
        rw [map_one,inv_one,mul_one]
      rw [he] at hh
      omega
  · let x : Group := ⟨!![0,1,0;1,0,0;0,0,1],by decide⟩
    have hx : x ^ 2 = 1 := by decide
    have hx1 : x ≠ 1 := by
      intro he
      exact zero_ne_one (congrArg (fun g : Group => g.val 0 0) he)
    have hb := pair_displacement x⁻¹ (v x)
      (by rw [inv_pow,hx,inv_one]) (by rw [←map_pow,hx,map_one])
      (inv_ne_one.mpr hx1)
    have hh := hcomm (x,1)
    have he : α (x,1) * (x,1)⁻¹ = (x⁻¹,v x) := by
      rw [huv]
      change (u 1 * x⁻¹,v x * 1⁻¹) = _
      rw [map_one,inv_one,one_mul,mul_one]
    rw [he] at hh
    omega

end BinaryLinearThree.SteinbergSquare
