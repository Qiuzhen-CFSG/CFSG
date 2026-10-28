module
public import Theory.Representation.BinaryTensorThree.OuterOffenders
public import Theory.Representation.BinaryTensorThree.PlaneFixed
public import Theory.Representation.TensorInvolutionDisplacement
public import Theory.SpecificGroups.PSL3Two.InvolutionConjugacy
public import Theory.Representation.BinaryTensorThree.Normalizer

/-!
# Six-spaces fixed by binary tensor near-offenders

The involution tensor formula makes a two-factor involution move four
dimensions. An inner involution moving at most three therefore acts on
one factor. The actual SL₃(2) involution conjugacy places a conjugate of
the paired plane-radical four-space in its fixed space. The checked outer
near-offender exclusion makes this applicable to every near-offender.
A fixed six-space is the whole involution fixed space by the lower bound
of three on displacement, so the inclusion holds in that exact six-space.

QuietTensorStrictR applies this geometry to the original minimal module,
lifting the conjugator through its full tensor action.
Source: Aschbacher--Smith H.4.10(3), H.4.12(3) and 8.3.11,
printed pp.384--385,726 (refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation.BinaryOffender
open Representation.BinaryOffender.NaturalTensor Representation.TensorInvolutionDisplacement
open scoped TensorProduct
namespace BinaryTensorThree

private theorem factor_displacement_one (a : Factor) (hs : a^2=1) (ha : a ≠ 1) :
    operatorFixedCodim a.toLinearMap = 1 := by
  have hs' : a.toLinearMap * a.toLinearMap = 1 := congrArg LinearEquiv.toLinearMap hs
  have hb := twice_displacement_le a.toLinearMap hs'
  have hd : Module.finrank (ZMod 2) Natural = 3 := by simp
  have hp : 0 < operatorFixedCodim a.toLinearMap := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hz' : (a.toLinearMap - 1).range = ⊥ := Submodule.finrank_eq_zero.mp hz
    have he : a.toLinearMap = 1 := sub_eq_zero.mp (LinearMap.range_eq_bot.mp hz')
    exact ha (LinearEquiv.toLinearMap_injective he)
  omega

private theorem base_involution_codim (a b : Factor) (ha : a^2=1) (hb : b^2=1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    fixedCodim action (zpowers (baseEmbedding (a,b))) = 4 := by
  have h := tensor_displacement_formula a.toLinearMap b.toLinearMap
    (congrArg LinearEquiv.toLinearMap ha) (congrArg LinearEquiv.toLinearMap hb)
  have he := operatorFixedCodim_eq_of_equiv
    (TensorProduct.map a.toLinearMap b.toLinearMap) (action (baseEmbedding (a,b)))
    coordinates (fun v => by
      change coordinates ((TensorProduct.congr a b) v) = baseAction (a,b) (coordinates v)
      simp [baseAction])
  rw [factor_displacement_one a ha ha1,factor_displacement_one b hb hb1] at h
  have hd : Module.finrank (ZMod 2) Natural = 3 := by simp
  rw [hd,he] at h
  rw [fixedCodim_zpowers_eq_displacement_rank]
  change operatorFixedCodim (action (baseEmbedding (a,b))) = 4
  omega

private def factorEquiv : Matrix.PSL3Two.SL ≃* Factor :=
  Matrix.PSL3Two.equivGL.trans
    ((Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := ZMod 2)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Natural))

private theorem factorEquiv_apply (g : Matrix.PSL3Two.SL) :
    factorEquiv g = Matrix.SpecialLinearGroup.toLin' g := by
  rw [factorEquiv,MulEquiv.trans_apply,Matrix.PSL3Two.equivGL_apply]
  rfl

private def root : Matrix.PSL3Two.SL := PlaneFixed.radical (Multiplicative.ofAdd ![1,0])
private theorem root_order : orderOf root = 2 :=
  orderOf_eq_prime (by decide +kernel : root^2=1) (by decide +kernel : root ≠ 1)

private theorem factor_root_conjugate (a : Factor) (ha : orderOf a = 2) :
    ∃ g : Factor, g * factorEquiv root * g⁻¹ = a := by
  let e := Matrix.PSL3Two.equiv.symm.trans factorEquiv
  obtain ⟨g,hg⟩ := Matrix.PSL3Two.involutions_conjugate
    (Matrix.PSL3Two.equiv root) (e.symm a)
    ((Matrix.PSL3Two.equiv.orderOf_eq root).trans root_order)
    ((e.symm.orderOf_eq a).trans ha)
  refine ⟨e g,?_⟩
  have he := congrArg e hg
  simpa only [MulAut.conj_apply,map_mul,map_inv,e,MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply,MulEquiv.apply_symm_apply] using he

private theorem root_fixes_square (X : Space) (hX : X ∈ PlaneFixed.square) :
    baseAction (factorEquiv root,1) X = X := by
  have hh := (PlaneFixed.radical_fixed_iff X).mpr hX (Multiplicative.ofAdd ![1,0],1)
  change action (PointParabolic.tensorHom (PlaneFixed.pair
    (root,PlaneFixed.radical 1))) X = X at hh
  rw [map_one,PlaneFixed.tensor_pair] at hh
  rw [←factorEquiv_apply,←factorEquiv_apply,map_one] at hh
  exact hh

private theorem left_involution_fixed_square (a : Factor) (ha : orderOf a=2) :
    ∃ g : Group, ∀ X ∈ PlaneFixed.square,
      action (baseEmbedding (a,1)) (action g X) = action g X := by
  obtain ⟨b,hb⟩ := factor_root_conjugate a ha
  refine ⟨baseEmbedding (b,1),fun X hX => ?_⟩
  have hc : (a,(1 : Factor))*(b,1) = (b,1)*(factorEquiv root,1) := by
    apply Prod.ext
    · change a*b = b*factorEquiv root
      rw [←hb,inv_mul_cancel_right]
    · simp
  change baseAction (a,1) (baseAction (b,1) X) = baseAction (b,1) X
  rw [←LinearEquiv.mul_apply,←map_mul,hc,map_mul,LinearEquiv.mul_apply,
    root_fixes_square X hX]

/-- A base involution moving at most three dimensions fixes a conjugate
of the marked four-space. The conjugator belongs to the same tensor group. -/
theorem inner_involution_fixed_square (t : Group) (ht : orderOf t=2)
    (hb : t ∈ baseEmbedding.range) (hc : fixedCodim action (zpowers t) ≤ 3) :
    ∃ g : Group, ∀ X ∈ PlaneFixed.square, action t (action g X) = action g X := by
  obtain ⟨⟨a,b⟩,rfl⟩ := hb
  have hi : Function.Injective baseEmbedding := fun _ _ h =>
    baseAction_injective (congrArg Subtype.val h)
  have ht2 : baseEmbedding (a,b)^2=1 := by simpa only [ht] using pow_orderOf_eq_one (baseEmbedding (a,b))
  have hs : (a,b)^2=1 := hi (by simpa only [map_pow,map_one] using ht2)
  have hsa : a^2=1 := congrArg Prod.fst hs
  have hsb : b^2=1 := congrArg Prod.snd hs
  have hone : a=1 ∨ b=1 := by
    by_contra! hn
    have hh := base_involution_codim a b hsa hsb hn.1 hn.2
    omega
  rcases hone with rfl | rfl
  · have hb2 : orderOf b=2 := by
      rw [orderOf_injective baseEmbedding hi] at ht
      simpa only [Prod.orderOf,orderOf_one,Nat.lcm_one_left,Nat.lcm_one_right] using ht
    obtain ⟨g,hg⟩ := left_involution_fixed_square b hb2
    refine ⟨swap*g,fun X hX => ?_⟩
    rw [map_mul,Module.End.mul_apply,action_swap]
    change baseAction (1,b) (flip (action g X)) = flip (action g X)
    exact (flip_baseAction (b,1) (action g X)).symm.trans (congrArg flip (hg X hX))
  · have ha2 : orderOf a=2 := by
      rw [orderOf_injective baseEmbedding hi] at ht
      simpa only [Prod.orderOf,orderOf_one,Nat.lcm_one_left,Nat.lcm_one_right] using ht
    exact left_involution_fixed_square a ha2

/-- A near-offender fixing a six-space forces that same six-space to
contain a conjugate of the marked plane-radical four-space. -/
theorem near_offender_fixed_contains_square
    (A : Subgroup Group) (hA : IsElementaryTwo A)
    (hnear : fixedCodim action A ≤ rank A + 1)
    (W : Submodule (ZMod 2) Space) (hW : 6 ≤ Module.finrank (ZMod 2) W)
    (hfix : W ≤ fixedSpace action A) :
    ∃ g : Group, ∀ X ∈ PlaneFixed.square, action g X ∈ W := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨t,ht,ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ht2 : orderOf t=2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian t ht) ht1
  have hbase := near_offender_le_base A hA hnear ht
  have hWF : W ≤ fixedSpace action (zpowers t) :=
    hfix.trans (fixedSpace_antitone action (zpowers_le.mpr ht))
  have hdim : Module.finrank (ZMod 2) Space=9 := by rw [Module.finrank_matrix]; norm_num
  have hd := fixedCodim_add_finrank action (zpowers t)
  have hle := Submodule.finrank_mono hWF
  have hc : fixedCodim action (zpowers t) ≤ 3 := by omega
  have hlo := involution_fixedCodim_ge_three t ht2
  have he : W = fixedSpace action (zpowers t) :=
    Submodule.eq_of_le_of_finrank_le hWF (by omega)
  obtain ⟨g,hg⟩ := inner_involution_fixed_square t ht2 hbase hc
  refine ⟨g,fun X hX => ?_⟩
  rw [he]
  exact (mem_fixedSpace_zpowers_iff action t _).mpr (hg X hX)

end BinaryTensorThree
