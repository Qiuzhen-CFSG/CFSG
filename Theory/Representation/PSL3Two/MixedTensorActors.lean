module
public import Theory.SpecificGroups.PSL3Two.InvolutoryCubicCommutator
public import Theory.Representation.PSL3Two.SteinbergSquareActors
public import Theory.Representation.PSL3Two.ProductCatalogue
public import Theory.Representation.PSL3Two.CubicSixSpace

/-!
# Excluding mixed binary linear-three tensor constituents

On a natural-or-dual tensor Steinberg module, a cubic in the first
factor moves16 dimensions and a cubic in the second moves18. These
values exclude factor exchanges. Every nontrivial involutory automorphism
of a factor has a cubic commutator. Thus an elementary actor of rank at
most four and fixed codimension at most eight centralizes the Steinberg
factor. Its faithful action on the remaining factor bounds its rank by
two, and the natural factor's cubic commutator contradicts that budget.

The constituent theorem constructs stability from degree24 and the
original actor bound, then restricts to the join with the normal square.
Both factor orientations and both natural/dual choices are included.
No faithful ambient action, tensor normalizer classification or assumed
constituent stability is needed. The original Chapter10 quiet seed is
the consumer in ModuleChoice.QuietSeedTensor and ModuleChoice.Source.
Source: Aschbacher--Smith D.3.7--9, printed pp.197--200, and original
3.2.6,10.1.1, printed pp.581,741.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.NaturalTensor
open Representation.QuadraticFourGroup.TensorClassification
open scoped TensorProduct
namespace BinaryLinearThree.MixedTensor
local instance : IsSimpleGroup Group := Atlas.Comparisons.Exceptional.sl3Two_simple

private theorem rTensor_displacement {U W : Type*}
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (a : Module.End (ZMod 2) U) :
    operatorFixedCodim (a.rTensor W) = Module.finrank (ZMod 2) W * operatorFixedCodim a := by
  have he : a.rTensor W - 1 = (a - 1).rTensor W := by ext x y; simp
  rw [operatorFixedCodim,he,LinearMap.rTensor_range]
  rw [LinearMap.finrank_range_of_inj
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)]
  rw [Module.finrank_tensorProduct]
  exact Nat.mul_comm _ _

private theorem lTensor_displacement {U W : Type*}
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (a : Module.End (ZMod 2) W) :
    operatorFixedCodim (a.lTensor U) = Module.finrank (ZMod 2) U * operatorFixedCodim a := by
  have he : a.lTensor U - 1 = (a - 1).lTensor U := by ext x y; simp
  rw [operatorFixedCodim,he,LinearMap.lTensor_range]
  rw [LinearMap.finrank_range_of_inj
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)]
  exact Module.finrank_tensorProduct

/-- A cubic on the natural or dual factor moves16 dimensions. -/
theorem first_cubic_displacement (a : ProductCatalogue.FactorType) (ha : a ≠ .steinberg)
    (g : Group) (hg : orderOf g = 3) :
    operatorFixedCodim (externalTensor a.action S (g,1)) = 16 := by
  have hc : Nat.card (zpowers g) = 3 := by rw [Nat.card_zpowers,hg]
  have hd : operatorFixedCodim (a.action g) = 2 := by
    have h := CubicSixSpace.natural_dual_codim (zpowers g) hc
    rw [fixedCodim_zpowers_eq_displacement_rank,fixedCodim_zpowers_eq_displacement_rank] at h
    cases a with
    | natural => exact h.1
    | dual => exact h.2
    | steinberg => exact (ha rfl).elim
  change operatorFixedCodim (TensorProduct.map (a.action g) (S 1)) = 16
  rw [map_one]
  change operatorFixedCodim ((a.action g).rTensor Steinberg) = 16
  rw [rTensor_displacement,finrank_steinberg,hd]

/-- A cubic on the Steinberg factor moves18 dimensions. -/
theorem second_cubic_displacement (a : ProductCatalogue.FactorType) (ha : a ≠ .steinberg)
    (g : Group) (hg : orderOf g = 3) :
    operatorFixedCodim (externalTensor a.action S (1,g)) = 18 := by
  have hc : Nat.card (zpowers g) = 3 := by rw [Nat.card_zpowers,hg]
  have hf := SteinbergStructure.ParabolicFactors.finrank_fixedSpace_order_three (zpowers g) hc
  have hh := fixedCodim_add_finrank S (zpowers g)
  rw [finrank_steinberg,hf,fixedCodim_zpowers_eq_displacement_rank] at hh
  have hd : operatorFixedCodim (S g) = 6 := by change operatorFixedCodim (S g) + 2 = 8 at hh; omega
  have he : Module.finrank (ZMod 2) a.Carrier = 3 := by
    rw [a.finrank]; cases a <;> simp_all [ProductCatalogue.FactorType.degree]
  change operatorFixedCodim (TensorProduct.map (a.action 1) (S g)) = 18
  rw [map_one]
  change operatorFixedCodim ((S g).lTensor a.Carrier) = 18
  rw [lTensor_displacement,he,hd]

/-- Distinct cubic displacements on the two factors exclude every faithful
elementary actor satisfying the source fixed-codimension budget. -/
theorem actor_budget_impossible_of_cubic_displacements
    {H V : Type*} [_root_.Group H] [Finite H]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V)
    (i : (Group × Group) →* H) (hi : Function.Injective i) [i.range.Normal]
    (hleft : ∀ g, orderOf g = 3 → operatorFixedCodim (ρ (i (g,1))) = 16)
    (hright : ∀ g, orderOf g = 3 → operatorFixedCodim (ρ (i (1,g))) = 18)
    (A : Subgroup H) (hA : IsElementaryTwo A)
    (hAC : A ⊓ centralizer (i.range : Set H) = ⊥)
    (hb : fixedCodim ρ A ≤ 2 * rank A) : False := by
  let N := i.range
  let b : (Group × Group) ≃* N := MonoidHom.ofInjective hi
  let α : A →* MulAut (Group × Group) :=
    (MulAut.congr b.symm).toMonoidHom.comp
      ((MulAut.conjNormal : H →* MulAut N).comp A.subtype)
  have hconj (a : A) (g : Group × Group) : i (α a g) = a * i g * (a : H)⁻¹ :=
    congrArg Subtype.val (b.apply_symm_apply (MulAut.conjNormal (a : H) (b g)))
  let : IsElementaryAbelian 2 A := hA.2
  have hsq (a : A) : α a * α a = 1 := by
    have hh : a ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (a : H) a.property)
    rw [←map_mul,←pow_two,hh,map_one]
  have hfaith (a : A) (ha : α a = 1) : a = 1 := by
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hAC]
    refine ⟨a.property,mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨g,rfl⟩
    have hh := hconj a g
    rw [ha] at hh
    change i g = a * i g * (a : H)⁻¹ at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  have hdiag (a : A) : ∃ u v : MulAut Group, α a = u.prodCongr v := by
    rcases AutomorphismSquare.normal_form Matrix.PSL3Two.center_eq_bot (α a) with h | ⟨u,v,he⟩
    · exact h
    · let x : Group := ⟨!![0,0,1;1,0,0;0,1,0],by decide⟩
      have hx : orderOf x = 3 := orderOf_eq_prime (by decide) (by
        intro hh
        exact zero_ne_one (congrArg (fun z : Group => z.val 0 0) hh))
      have hh := fixedCodim_zpowers_conj ρ (i (x,1)) a
      rw [←hconj,fixedCodim_zpowers_eq_displacement_rank,
        fixedCodim_zpowers_eq_displacement_rank] at hh
      have he' : α a (x,1) = (1,v x) := by rw [he]; change (u 1,v x) = _; rw [map_one]
      change operatorFixedCodim (ρ (i (α a (x,1)))) =
        operatorFixedCodim (ρ (i (x,1))) at hh
      rw [he',hleft x hx,hright (v x) ((v.orderOf_eq x).trans hx)] at hh
      omega
  let u (a : A) : MulAut Group := Classical.choose (hdiag a)
  let v (a : A) : MulAut Group := Classical.choose (Classical.choose_spec (hdiag a))
  have he (a : A) : α a = (u a).prodCongr (v a) :=
    Classical.choose_spec (Classical.choose_spec (hdiag a))
  have hpair (a : A) (x y : Group) : α a (x,y) = (u a x,v a y) := by
    rw [he]
    rfl
  have hsecond (a : A) : v a = 1 := by
    by_contra hv
    have hv2 : v a * v a = 1 := by
      apply MulEquiv.ext
      intro x
      have hh := congrArg Prod.snd (DFunLike.congr_fun (hsq a) (1,x))
      simpa only [MulAut.mul_apply,MulAut.one_apply,hpair] using hh
    obtain ⟨x,hx⟩ := Matrix.PSL3Two.involutory_automorphism_cubic_commutator (v a) hv2 hv
    have hh := fixedCodim_commutator_le_twice ρ a (i (1,x))
    have hc : (a : H) * i (1,x) * (a : H)⁻¹ * (i (1,x))⁻¹ = i (1,v a x * x⁻¹) := by
      rw [←hconj,←map_inv,←map_mul,he]
      congr 1
      change (u a 1 * 1⁻¹,v a x * x⁻¹) = _
      rw [map_one,inv_one,mul_one]
    rw [hc,fixedCodim_zpowers_eq_displacement_rank] at hh
    change operatorFixedCodim (ρ (i (1,v a x * x⁻¹))) ≤ _ at hh
    rw [hright _ hx] at hh
    let c : Group ≃* BinaryTensorThree.Factor := Matrix.PSL3Two.equivGL.trans
      ((Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := ZMod 2)).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) BinaryTensorThree.Natural))
    have hr := BinaryTensorThree.rank_le_four_of_faithful_on_tensor_base N A hA hAC
      (b.symm.trans (c.prodCongr c))
    have hd := fixedCodim_mono ρ (zpowers_le.mpr a.property)
    omega
  let f : A →* MulAut Group := {
    toFun := u
    map_one' := by
      apply MulEquiv.ext
      intro x
      have hh := congrArg Prod.fst (DFunLike.congr_fun α.map_one (x,1))
      simpa only [MulAut.one_apply,hpair] using hh
    map_mul' a c := by
      apply MulEquiv.ext
      intro x
      have hh := congrArg Prod.fst (DFunLike.congr_fun (α.map_mul a c) (x,1))
      simpa only [MulAut.mul_apply,MulAut.one_apply,hpair] using hh }
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    apply mem_bot.mpr
    apply hfaith
    rw [he,hsecond]
    change u a = 1 at ha
    rw [ha]
    rfl
  have hfr : primeRank 2 (MulAut Group) = 2 := by
    rw [primeRank_equiv 2 (MulAut.congr Matrix.PSL3Two.equiv)]
    exact Matrix.PSL3Even.automorphism_two_rank_eq_of_card_two (ZMod 2) (by simp)
  have hr : rank A ≤ 2 := by
    have hE : IsElementaryAbelian 2 f.range :=
      IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    have hc := (primeRank_le_iff_elementary_card_le _).mp hfr.le f.range hE
    rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv] at hc
    have hh := Nat.log_mono_right (b := 2) hc
    simpa only [rank,Nat.log_pow (by decide : 1 < 2)] using hh
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  let a' : A := ⟨a,ha⟩
  have hu1 : u a' ≠ 1 := by
    intro hh
    exact ha1 (congrArg Subtype.val (hf (hh.trans f.map_one.symm)))
  have hu2 : u a' * u a' = 1 := by
    change f a' * f a' = 1
    have hh : a' ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a ha)
    rw [←map_mul,←pow_two,hh,map_one]
  obtain ⟨x,hx⟩ := Matrix.PSL3Two.involutory_automorphism_cubic_commutator (u a') hu2 hu1
  have hh := fixedCodim_commutator_le_twice ρ a (i (x,1))
  have hc : a * i (x,1) * a⁻¹ * (i (x,1))⁻¹ = i (u a' x * x⁻¹,1) := by
    rw [←hconj a',←map_inv,←map_mul,he]
    congr 1
    change (u a' x * x⁻¹,v a' 1 * 1⁻¹) = _
    rw [map_one,inv_one,mul_one]
  rw [hc,fixedCodim_zpowers_eq_displacement_rank] at hh
  change operatorFixedCodim (ρ (i (u a' x * x⁻¹,1))) ≤ _ at hh
  rw [hleft _ hx] at hh
  have hd := fixedCodim_mono ρ (zpowers_le.mpr ha)
  omega

private theorem tensor_comm_displacement (a b : ProductCatalogue.FactorType)
    (g h : Group) :
    operatorFixedCodim (externalTensor a.action b.action (g,h)) =
      operatorFixedCodim (externalTensor b.action a.action (h,g)) := by
  apply operatorFixedCodim_eq_of_equiv _ _ (TensorProduct.comm (ZMod 2) a.Carrier b.Carrier)
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y => rfl

/-- All four mixed natural-or-dual/Steinberg rows are excluded with the
original elementary actor and its full normal-square centralizer kernel. -/
theorem actor_budget_impossible
    {H V : Type*} [_root_.Group H] [Finite H]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V)
    (i : (Group × Group) →* H) (hi : Function.Injective i) [i.range.Normal]
    (a b : ProductCatalogue.FactorType) (hdegree : a.degree * b.degree = 24)
    (e : Representation.Equiv (ρ.comp i) (externalTensor a.action b.action))
    (A : Subgroup H) (hA : IsElementaryTwo A)
    (hAC : A ⊓ centralizer (i.range : Set H) = ⊥)
    (hb : fixedCodim ρ A ≤ 2 * rank A) : False := by
  have hd (g : Group × Group) : operatorFixedCodim (ρ (i g)) =
      operatorFixedCodim (externalTensor a.action b.action g) :=
    operatorFixedCodim_eq_of_equiv _ _ e.toLinearEquiv
      (fun v => LinearMap.congr_fun (e.isIntertwining' g) v)
  by_cases ha : a = .steinberg
  · subst a
    have hbtype : b ≠ .steinberg := by
      intro he
      subst b
      norm_num [ProductCatalogue.FactorType.degree] at hdegree
    let c : (Group × Group) ≃* (Group × Group) := MulEquiv.prodComm
    let j := i.comp c.toMonoidHom
    have hj : Function.Injective j := hi.comp c.injective
    have hjr : j.range = i.range := by
      ext g
      constructor
      · rintro ⟨x,rfl⟩
        exact ⟨c x,rfl⟩
      · rintro ⟨x,rfl⟩
        exact ⟨c.symm x,by change i (c (c.symm x)) = i x; rw [c.apply_symm_apply]⟩
    let : j.range.Normal := hjr.symm ▸ inferInstanceAs i.range.Normal
    apply actor_budget_impossible_of_cubic_displacements ρ j hj ?_ ?_ A hA (hjr.symm ▸ hAC) hb
    · intro g hg
      change operatorFixedCodim (ρ (i (1,g))) = 16
      rw [hd,tensor_comm_displacement]
      exact first_cubic_displacement b hbtype g hg
    · intro g hg
      change operatorFixedCodim (ρ (i (g,1))) = 18
      rw [hd,tensor_comm_displacement]
      exact second_cubic_displacement b hbtype g hg
  · have hsb : b = .steinberg := by
      cases a <;> cases b <;> simp_all [ProductCatalogue.FactorType.degree]
    subst b
    apply actor_budget_impossible_of_cubic_displacements ρ i hi ?_ ?_ A hA hAC hb
    · intro g hg
      rw [hd]
      exact first_cubic_displacement a ha g hg
    · intro g hg
      rw [hd]
      exact second_cubic_displacement a ha g hg

/-- An actual mixed constituent contradicts the ambient elementary-actor
budget. Its degree forces actor stability before the restriction to the
join with the original normal square; no ambient faithfulness is assumed. -/
theorem constituent_impossible
    {H V W : Type*} [_root_.Group H] [Finite H]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H V)
    (i : (Group × Group) →* H) (hi : Function.Injective i) [i.range.Normal]
    (σ : Representation (ZMod 2) (Group × Group) W)
    (hirr : σ.IsIrreducible)
    (a₀ b₀ : ProductCatalogue.FactorType) (hdegree : a₀.degree * b₀.degree = 24)
    (b : σ.Equiv (externalTensor a₀.action b₀.action))
    (f : σ.IntertwiningMap (ρ.comp i)) (hf : Function.Injective f)
    (A : Subgroup H) (hA : IsElementaryTwo A)
    (hAC : A ⊓ centralizer (i.range : Set H) = ⊥)
    (hb : fixedCodim ρ A ≤ 2 * rank A) : False := by
  let N := i.range
  let e : N ≃* (Group × Group) := (MonoidHom.ofInjective hi).symm
  let U : Subrepresentation (ρ.comp N.subtype) := {
    toSubmodule := f.range.toSubmodule
    apply_mem_toSubmodule g v hv := by
      obtain ⟨k,hk⟩ := g.property
      change ρ g.val v ∈ f.range.toSubmodule
      rw [←hk]
      exact f.range.apply_mem_toSubmodule k hv }
  let d : W ≃ₗ[ZMod 2] U.toSubmodule := LinearEquiv.ofInjective f.toLinearMap hf
  let eU : Representation.Equiv (σ.comp e.toMonoidHom) U.toRepresentation := .mk d (by
    intro g
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    have he : i (e g) = (g : H) := congrArg Subtype.val
      ((MonoidHom.ofInjective hi).apply_symm_apply g)
    change f (σ (e g) w) = ρ g.val (f w)
    rw [←he]
    exact LinearMap.congr_fun (f.isIntertwining' (e g)) w)
  have hiU : U.toRepresentation.IsIrreducible :=
    (RepEquiv.ofRepresentationEquiv eU.symm).irreducible_of_euqiv
      ((irreducible_comp_surjective_iff e.toMonoidHom e.surjective σ).mpr hirr)
  let c : Group ≃* BinaryTensorThree.Factor := Matrix.PSL3Two.equivGL.trans
    ((Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := ZMod 2)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) BinaryTensorThree.Natural))
  have hr := BinaryTensorThree.rank_le_four_of_faithful_on_tensor_base N A hA hAC
    (e.trans (c.prodCongr c))
  have hd : Module.finrank (ZMod 2) U.toSubmodule = 24 := by
    rw [←d.finrank_eq,ProductCatalogue.finrank_of_marking σ a₀ b₀ b,hdegree]
  have hstable : ∀ a ∈ A, U.toSubmodule.map (ρ a) = U.toSubmodule := by
    intro a ha
    apply map_constituent_eq_self_of_displacement_lt ρ N a U hiU
    have hh := NaturalTensor.operatorFixedCodim_le_fixedCodim ρ A ha
    change NaturalTensor.operatorFixedCodim (ρ a) < Module.finrank (ZMod 2) U.toSubmodule
    rw [hd]
    omega
  let J := A ⊔ N
  have hAJ : A ≤ J := le_sup_left
  have hNJ : N ≤ J := le_sup_right
  let U' : Subrepresentation (ρ.comp J.subtype) := {
    toSubmodule := U.toSubmodule
    apply_mem_toSubmodule g v hv := by
      obtain ⟨a,ha,n,hn,hg⟩ := mem_sup_of_normal_right.mp g.property
      change ρ g.val v ∈ U.toSubmodule
      rw [←hg,map_mul,Module.End.mul_apply,←hstable a ha]
      exact ⟨ρ n v,U.apply_mem_toSubmodule ⟨n,hn⟩ hv,rfl⟩ }
  let j : (Group × Group) →* J := i.codRestrict J (fun g => hNJ ⟨g,rfl⟩)
  have hjr : j.range = N.subgroupOf J := by
    ext g
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x,rfl⟩
    · rintro ⟨x,hx⟩
      exact ⟨x,Subtype.ext hx⟩
  let : j.range.Normal := hjr.symm ▸ inferInstanceAs (N.subgroupOf J).Normal
  let τ := U'.toRepresentation
  let d' : σ.Equiv (τ.comp j) := .mk d (by
    intro g
    apply LinearMap.ext
    intro w
    exact Subtype.ext (LinearMap.congr_fun (f.isIntertwining' g) w))
  have hj : Function.Injective j := by
    intro x y he
    exact hi (congrArg Subtype.val he)
  let A' := A.subgroupOf J
  let : IsElementaryAbelian 2 A := hA.2
  have hA' : IsElementaryTwo A' := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf hAJ⟩
    intro hz
    apply hA.1
    have hh := congrArg (map J.subtype) hz
    simpa only [A',map_subgroupOf_eq_of_le hAJ,Subgroup.map_bot] using hh
  have hAC' : A' ⊓ centralizer (j.range : Set J) = ⊥ := by
    rw [hjr]
    apply bot_unique
    rintro a ⟨ha,hcent⟩
    apply mem_bot.mpr
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hAC]
    exact ⟨ha,fun n hn => congrArg Subtype.val (hcent ⟨n,hNJ hn⟩ hn)⟩
  have hb' : fixedCodim τ A' ≤ 2 * rank A' := by
    rw [rank_subgroupOf hAJ]
    have hh := fixedCodim_subrepresentation_le (ρ.comp J.subtype) U' A'
    rw [fixedCodim_subgroupOf ρ hAJ] at hh
    exact hh.trans hb
  exact actor_budget_impossible τ j hj a₀ b₀ hdegree (d'.symm.trans b) A' hA' hAC' hb'


end BinaryLinearThree.MixedTensor
