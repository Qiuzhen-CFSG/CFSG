module

public import Theory.Representation.SmallBinaryFiveOvergroup
public import Theory.Representation.BinaryOffender.InvolutionFixedKernel
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The intrinsic involution fixed-plane model in the marked-five row

A faithful binary four-space with quadratic ratio two has a plane fixed by
any involution. If the actor has a normal subgroup of order five, the kernel
of its centralizer on that plane has order at most two: it is elementary
abelian, while every two-subgroup is cyclic. Thus the centralizer has order
dividing twelve, and a non-two subgroup containing a four has the actual
symmetric-three quotient by its two-core.

Source application: Aschbacher--Smith 15.1.14 and 15.2.28, printed pp.1090
and 1119. The argument uses the original action, with no semilinear model.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01.SourceFifteenModel
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
  (h4 : Module.finrank (ZMod 2) W = 4)
  (P : Subgroup D) [P.Normal] (hP : Nat.card P = 5)

include h4 in
/-- Every involution in the ratio-two four-space fixes a plane. -/
theorem involution_fixed_dimension (hq : quadraticRatio ρ = 2)
    (t : D) (ht : orderOf t = 2) :
    Module.finrank (ZMod 2) (fixedSpace ρ (zpowers t)) = 2 := by
  obtain ⟨he,hr,hquad,hhalf⟩ := involution_actor_rank_and_fixedCodim ρ t ht
  have hlo : quadraticRatio ρ ≤ actionRatio ρ (zpowers t) :=
    iInf_le_of_le _ (iInf_le_of_le ⟨he,hquad⟩ le_rfl)
  rw [hq,actionRatio,hr,Nat.cast_one,div_one] at hlo
  have hlo' : 2 ≤ fixedCodim ρ (zpowers t) := by exact_mod_cast hlo
  have hsum := fixedCodim_add_finrank ρ (zpowers t)
  omega

omit [Finite D] [FiniteDimensional (ZMod 2) W] in
/-- The centralizer preserves the literal involution fixed space. -/
theorem centralizer_stabilizes (t : D) :
    centralizer {t} ≤ subspaceStabilizer ρ (fixedSpace ρ (zpowers t)) := by
  apply le_subspaceStabilizer
  intro g hg v hv
  rw [mem_fixedSpace_zpowers_iff] at hv ⊢
  rw [← Module.End.mul_apply, ← map_mul,
    ← mem_centralizer_singleton_iff.mp hg, map_mul, Module.End.mul_apply, hv]

include hf h4 hP

/-- The pointwise kernel on the fixed plane has order dividing two. -/
theorem involution_kernel_card_dvd (t : D) (ht : t ^ 2 = 1) :
    Nat.card (involutionFixedKernel ρ t) ∣ 2 := by
  let := involutionFixedKernel_elementary ρ hf t ht
  let := (SmallBinaryFiveOvergroup.two_subgroup ρ hf h4 P hP
    (involutionFixedKernel ρ t) (IsElementaryAbelian.isPGroup 2 _)).1
  have he := IsElementaryAbelian.exponent_dvd_p 2 (involutionFixedKernel ρ t)
  rwa [IsCyclic.exponent_eq_card] at he

/-- Any subgroup of the involution centralizer has the same kernel bound. -/
theorem subgroup_kernel_card_dvd (t : D) (ht : t ^ 2 = 1)
    (A : Subgroup D) (hA : A ≤ centralizer {t}) :
    Nat.card (subspaceKernel ρ (fixedSpace ρ (zpowers t)) A) ∣ 2 := by
  apply (card_dvd_of_le (show subspaceKernel ρ (fixedSpace ρ (zpowers t)) A ≤
    involutionFixedKernel ρ t from fun _ h => ⟨hA h.1,h.2⟩)).trans
  exact involution_kernel_card_dvd ρ hf h4 P hP t ht

omit hf h4 hP [Finite D] in
private def plane_permutations (U : Submodule (ZMod 2) W)
    (hU : Module.finrank (ZMod 2) U = 2) :
    (Module.End (ZMod 2) U)ˣ ≃* Equiv.Perm (Fin 3) :=
  let e : U ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space 2 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hU)
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U).trans
    ((BinaryLinear.SmallParabolicLevi.linearGroupCongr e).trans
      BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree)

omit hf hP in
/-- The literal action image on the fixed plane has order dividing six. -/
theorem restricted_image_card_dvd (hq : quadraticRatio ρ = 2)
    (t : D) (ht : orderOf t = 2) (A : Subgroup D) :
    Nat.card (restrictedSubgroup ρ (fixedSpace ρ (zpowers t)) A) ∣ 6 := by
  let U := fixedSpace ρ (zpowers t)
  let I := restrictedSubgroup ρ U A
  let e := plane_permutations U (involution_fixed_dimension ρ h4 hq t ht)
  let j : I →* Equiv.Perm (Fin 3) :=
    e.toMonoidHom.comp ((subspaceActionImage ρ U).subtype.comp I.subtype)
  have hj : Function.Injective j :=
    e.injective.comp (Subtype.val_injective.comp Subtype.val_injective)
  have hd := card_dvd_of_injective j hj
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  exact hc ▸ hd

/-- Every subgroup of the involution centralizer has order dividing twelve. -/
theorem subgroup_card_dvd (hq : quadraticRatio ρ = 2)
    (t : D) (ht : orderOf t = 2) (A : Subgroup D) (hA : A ≤ centralizer {t}) :
    Nat.card A ∣ 12 := by
  have hk := subgroup_kernel_card_dvd ρ hf h4 P hP t
    (ht ▸ pow_orderOf_eq_one t) A hA
  have hi := restricted_image_card_dvd ρ h4 hq t ht A
  have he := card_subspaceKernel_mul_image ρ (fixedSpace ρ (zpowers t)) A
    (hA.trans (centralizer_stabilizes ρ t))
  rw [← he]
  exact Nat.mul_dvd_mul hk hi

/-- A four-subgroup has an involution as its image on the fixed plane. -/
theorem four_subgroup_image_card (hq : quadraticRatio ρ = 2)
    (t : D) (ht : orderOf t = 2) (S : Subgroup D)
    (hS : S ≤ centralizer {t}) (hSc : Nat.card S = 4) :
    Nat.card (restrictedSubgroup ρ (fixedSpace ρ (zpowers t)) S) = 2 := by
  have hk := subgroup_kernel_card_dvd ρ hf h4 P hP t
    (ht ▸ pow_orderOf_eq_one t) S hS
  have hi := restricted_image_card_dvd ρ h4 hq t ht S
  have he := card_subspaceKernel_mul_image ρ (fixedSpace ρ (zpowers t)) S
    (hS.trans (centralizer_stabilizes ρ t))
  rw [hSc] at he
  rcases (Nat.dvd_prime Nat.prime_two).mp hk with hk | hk
  · rw [hk,one_mul] at he
    rw [he] at hi
    norm_num at hi
  · rw [hk] at he
    omega

/-- A non-two subgroup containing a four fills the order-twelve centralizer. -/
theorem subgroup_card_twelve (hq : quadraticRatio ρ = 2)
    (t : D) (ht : orderOf t = 2) (A : Subgroup D) (hA : A ≤ centralizer {t})
    (hfour : 4 ∣ Nat.card A) (hn : ¬ IsPGroup 2 A) : Nat.card A = 12 := by
  have hd := subgroup_card_dvd ρ hf h4 P hP hq t ht A hA
  have hc := Nat.le_of_dvd (by decide : 0 < 12) hd
  have hp := Nat.card_pos (α := A)
  have hcases : Nat.card A = 4 ∨ Nat.card A = 8 ∨ Nat.card A = 12 := by omega
  rcases hcases with h | h | h
  · exact (hn (IsPGroup.of_card (n := 2) h)).elim
  · exact (hn (IsPGroup.of_card (n := 3) h)).elim
  · exact h

/-- An order-twelve subgroup has the full six-element action on the plane. -/
theorem twelve_subgroup_image_card (hq : quadraticRatio ρ = 2)
    (t : D) (ht : orderOf t = 2) (A : Subgroup D)
    (hA : A ≤ centralizer {t}) (hAc : Nat.card A = 12) :
    Nat.card (restrictedSubgroup ρ (fixedSpace ρ (zpowers t)) A) = 6 := by
  have hk := subgroup_kernel_card_dvd ρ hf h4 P hP t
    (ht ▸ pow_orderOf_eq_one t) A hA
  have hi := restricted_image_card_dvd ρ h4 hq t ht A
  have he := card_subspaceKernel_mul_image ρ (fixedSpace ρ (zpowers t)) A
    (hA.trans (centralizer_stabilizes ρ t))
  rw [hAc] at he
  rcases (Nat.dvd_prime Nat.prime_two).mp hk with hk | hk
  · rw [hk,one_mul] at he
    rw [he] at hi
    norm_num at hi
  · rw [hk] at he
    omega

/-- The actual two-core quotient of the non-two centralizer subgroup is S₃. -/
theorem subgroup_quotient_symmetric_three (hq : quadraticRatio ρ = 2)
    (t : D) (ht : orderOf t = 2) (A : Subgroup D) (hA : A ≤ centralizer {t})
    (hfour : 4 ∣ Nat.card A) (hn : ¬ IsPGroup 2 A) :
    Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) := by
  let U := fixedSpace ρ (zpowers t)
  let I := restrictedSubgroup ρ U A
  have hAU : A ≤ subspaceStabilizer ρ U := hA.trans (centralizer_stabilizes ρ t)
  have hAc := subgroup_card_twelve ρ hf h4 P hP hq t ht A hA hfour hn
  have hIc : Nat.card I = 6 := twelve_subgroup_image_card ρ hf h4 P hP hq t ht A hA hAc
  let e := plane_permutations U (involution_fixed_dimension ρ h4 hq t ht)
  let j : I →* Equiv.Perm (Fin 3) :=
    e.toMonoidHom.comp ((subspaceActionImage ρ U).subtype.comp I.subtype)
  have hj : Function.Injective j :=
    e.injective.comp (Subtype.val_injective.comp Subtype.val_injective)
  have hjs : Function.Surjective j := by
    apply ((Nat.bijective_iff_injective_and_card j).mpr ⟨hj,?_⟩).surjective
    rw [hIc]
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  let a := subgroupActionHom ρ U A hAU
  let b := e.toMonoidHom.comp (subspaceActionImage ρ U).subtype
  let f := b.comp a
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := hjs y
    have hxmem : x.val ∈ a.range := by
      rw [subgroupActionHom_range ρ U A hAU]
      exact x.property
    obtain ⟨g,hg⟩ := hxmem
    refine ⟨g,?_⟩
    change b (a g) = y
    rw [hg]
    exact hx
  have hker : f.ker = a.ker :=
    MonoidHom.ker_comp_of_injective a b (e.injective.comp Subtype.val_injective)
  have hk : Nat.card a.ker ∣ 2 := by
    have h := subgroup_kernel_card_dvd ρ hf h4 P hP t
      (ht ▸ pow_orderOf_eq_one t) A hA
    rw [← subgroupActionHom_ker ρ U A hAU,
      card_map_of_injective A.subtype_injective] at h
    exact h
  have hkp : IsPGroup 2 f.ker := by
    rw [hker]
    exact IsPGroup.of_card_dvd_pow (n := 1) hk
  have hcore := ker_eq_twoCore_of_surjective_perm_three f hfs hkp
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hfs)⟩

omit hf h4 hP [Finite D] [FiniteDimensional (ZMod 2) W] in
private theorem two_generator (R : Subgroup D) (hR : Nat.card R = 2) :
    ∃ t : D, orderOf t = 2 ∧ zpowers t = R := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsCyclic R := isCyclic_of_prime_card hR
  obtain ⟨t,ht⟩ := R.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  refine ⟨t,?_,ht⟩
  rw [← Nat.card_zpowers,ht,hR]

omit hf hP in
/-- The literal fixed space of any order-two subgroup is a plane. -/
theorem two_subgroup_fixed_dimension (hq : quadraticRatio ρ = 2)
    (R : Subgroup D) (hR : Nat.card R = 2) :
    Module.finrank (ZMod 2) (fixedSpace ρ R) = 2 := by
  obtain ⟨t,ht,rfl⟩ := two_generator R hR
  exact involution_fixed_dimension ρ h4 hq t ht

omit hf h4 hP [Finite D] [FiniteDimensional (ZMod 2) W] in
private theorem normalizer_centralizes_generator (R : Subgroup D)
    (hR : Nat.card R = 2) (t : D) (ht : zpowers t = R) :
    normalizer (R : Set D) ≤ centralizer {t} := by
  intro a ha
  rw [mem_centralizer_singleton_iff]
  exact (mem_centralizer_iff.mp ((normalizer_le_centralizer_of_card_two R hR) ha)
    t (ht ▸ mem_zpowers t)).symm

/-- A four-subgroup normalizing the order-two actor has image of order two. -/
theorem normalizer_four_image_card (hq : quadraticRatio ρ = 2)
    (R : Subgroup D) (hR : Nat.card R = 2) (S : Subgroup D)
    (hS : S ≤ normalizer (R : Set D)) (hSc : Nat.card S = 4) :
    Nat.card (restrictedSubgroup ρ (fixedSpace ρ R) S) = 2 := by
  obtain ⟨t,ht,he⟩ := two_generator R hR
  rw [← he]
  exact four_subgroup_image_card ρ hf h4 P hP hq t ht S
    (hS.trans (normalizer_centralizes_generator R hR t he)) hSc

/-- The order-two normalizer has the actual S₃ quotient on every non-two
subgroup containing a subgroup of order four. -/
theorem normalizer_quotient_symmetric_three (hq : quadraticRatio ρ = 2)
    (R : Subgroup D) (hR : Nat.card R = 2)
    (A : Subgroup D) (hA : A ≤ normalizer (R : Set D))
    (S : Subgroup D) (hSA : S ≤ A) (hSc : Nat.card S = 4)
    (hn : ¬ IsPGroup 2 A) :
    Nat.card A = 12 ∧ Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨t,ht,he⟩ := two_generator R hR
  have hAt := hA.trans (normalizer_centralizes_generator R hR t he)
  have hfour : 4 ∣ Nat.card A := hSc ▸ card_dvd_of_le hSA
  exact ⟨subgroup_card_twelve ρ hf h4 P hP hq t ht A hAt hfour hn,
    subgroup_quotient_symmetric_three ρ hf h4 P hP hq t ht A hAt hfour hn⟩

end CFSG.Quasithin.Chapter15.Section01.SourceFifteenModel
