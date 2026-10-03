module
public import Stellmacher.SectionOne.WreathSmallDisplacementCard
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupAction.FourElementInvolutionLines
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.WreathTwoOddCoreImageDichotomy

/-!
# A wreath Sylow four-group fixing a coatom

Let a finite group K isomorphic to SL₂(2) wreath C₂ act on a finite
elementary abelian two-group V. If a normal elementary four-subgroup of a
Sylow two-subgroup fixes a subgroup of index at most two pointwise, then
the odd core of K acts trivially on V. Consequently the actual action image
is a two-group. No faithful-action or irreducibility assumption is made.

The moving subgroup M=[V,O₂′(K)] is K-invariant. Coprime splitting makes its
odd-core fixed subgroup trivial. The normal four contains an involution
inverting the odd core; its displacement on M has order at most two because
it fixes the induced coatom. The inversion rank formula therefore gives
|M|≤4. The full-wreath normal-kernel dichotomy says that the odd-core image
is trivial or the actual action image has order divisible by nine. The
latter requires a faithful binary module of order at least sixteen, so the
odd core fixes M. Coprime splitting now gives M=1. Its index-eight core then
forces the full action image to be a two-group.

Source: Stellmacher (10.1), printed p.60/PDF p.50 of
`refs/files/stellmacher-n-group.pdf`, the paragraph excluding alternative
(5). The Section Ten consumer supplies the actual first-module image and
the coatom in the Frattini quotient of the terminal Q/V. This module keeps
the supplied action unchanged and proves the missing action calculation.
-/

namespace Stellmacher.SectionOne

open scoped IsMulCommutative
universe u

private theorem elementary_subgroup
    {V : Type*} [Group V] [IsElementaryAbelian 2 V] (M : Subgroup V) :
    IsElementaryAbelian 2 M where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro m
    exact Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (m : V))

private theorem coatom_involution_displacement_bound
    {K M : Type u} [Group K] [Finite K] [Group M] [Finite M]
    [IsElementaryAbelian 2 M] [MulDistribMulAction K M]
    (x : K) (hx : IsInvolution x) (C : Subgroup M)
    (hindex : C.index ≤ 2) (hfixed : ∀ c ∈ C, x • c = c) :
    Nat.card (commutatorAction (Subgroup.zpowers x) M) ≤ 2 := by
  classical
  by_cases htriv : Subsingleton M
  · let _ := htriv
    have hcard : Nat.card (commutatorAction (Subgroup.zpowers x) M) = 1 := Nat.card_unique
    omega
  let _ : Nontrivial M := not_subsingleton_iff_nontrivial.mp htriv
  let R := Subgroup.zpowers x
  let F := FixedPoints.subgroup R M
  have hCF : C ≤ F := by
    intro c hc r
    exact smul_eq_self_of_mem_zpowers r.property (hfixed c hc)
  have hFindex : F.index ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero C.index_ne_zero_of_finite) (Subgroup.index_dvd_of_le hCF)).trans hindex
  have hcardR : Nat.card R = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx.2 hx.1]
  have hprod := (card_two_action_fixed_commutator_card_data
    (U := M) (⟨x,Subgroup.mem_zpowers x⟩ : R)
    ⟨fun hh => hx.1 (congrArg Subtype.val hh), Subtype.ext hx.2⟩ hcardR).1
  have hcount := F.card_mul_index
  have hpos : 0 < Nat.card F := Nat.card_pos
  change Nat.card M = Nat.card F * Nat.card (commutatorAction R M) at hprod
  nlinarith

private theorem moving_module_small
    {K V : Type u} [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (model : Nonempty (K ≃* Stellmacher.Later.SL2TwoWreathC2))
    (S : Sylow 2 K) (A : Subgroup K) (hAS : A ≤ (S : Subgroup K))
    (hAN : (A.subgroupOf (S : Subgroup K)).Normal)
    (hAE : IsElementaryAbelian 2 A) (hAc : Nat.card A = 4)
    (C : Subgroup V) (hindex : C.index ≤ 2)
    (hfixed : ∀ a ∈ A, ∀ c ∈ C, a • c = c) :
    Nat.card (commutatorAction (oddCore K) V) ≤ 4 := by
  classical
  let O := oddCore K
  let M := commutatorAction O V
  let _ : O.Normal := pPrimeCore_normal
  have hnorm : (⊤ : Subgroup K) ≤ Subgroup.normalizer (O : Set K) := by
    rw [Subgroup.normalizer_eq_top]
  have hinv := commutatorAction_isInvariant_of_normalizing_actor (V := V) (⊤ : Subgroup K) O hnorm
  let _ : IsInvariant K V M := ⟨fun k v => hinv.invariant ⟨k,Subgroup.mem_top k⟩ v⟩
  let _ : IsElementaryAbelian 2 M := elementary_subgroup M
  obtain ⟨hOc,x,hxA,hx,hxO⟩ := Theory.GroupTheory.wreathTwo_exists_actor_oddCore_inverter
    model S A hAS hAN hAE hAc
  have hodd : Odd (Nat.card O) := by rw [show Nat.card O = 9 from hOc]; decide
  have hcop : Nat.Coprime (Nat.card O) (Nat.card V) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hn]
    exact hodd.coprime_two_right.pow_right n
  have hcompl := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := V) (A := O) (Group.isSolvable_of_comm fun v w => mul_comm v w) hcop inferInstance
  have hMfixed : FixedPoints.subgroup O M = ⊥ := by
    apply bot_unique
    intro m hm
    apply Subtype.ext
    have hvfixed : (m : V) ∈ FixedPoints.subgroup O V := by
      intro o
      exact congrArg Subtype.val (hm o)
    exact hcompl.disjoint.le_bot ⟨hvfixed,m.property⟩
  have hMCindex : (C.subgroupOf M).index ≤ 2 := by
    let _ : C.Normal := Subgroup.normal_of_isMulCommutative C
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero C.index_ne_zero_of_finite) (C.relIndex_dvd_index_of_normal M)).trans hindex
  have hdx := coatom_involution_displacement_bound x hx (C.subgroupOf M) hMCindex
    (fun c hc => Subtype.ext (hfixed x hxA (c : V) hc))
  have hsquare := invertedOddSubgroup_card_eq_commutator_sq O hodd x hx hxO hMfixed
  rw [hsquare]
  nlinarith


public theorem wreath_oddCore_fixes_of_fixed_coatom
    {K V : Type u} [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (model : Nonempty (K ≃* Stellmacher.Later.SL2TwoWreathC2))
    (S : Sylow 2 K) (A : Subgroup K) (hAS : A ≤ (S : Subgroup K))
    (hAN : (A.subgroupOf (S : Subgroup K)).Normal)
    (hAE : IsElementaryAbelian 2 A) (hAc : Nat.card A = 4)
    (C : Subgroup V) (hindex : C.index ≤ 2)
    (hfixed : ∀ a ∈ A, ∀ c ∈ C, a • c = c) :
    ∀ o ∈ oddCore K, ∀ v : V, o • v = v := by
  classical
  have hsmall := moving_module_small model S A hAS hAN hAE hAc C hindex hfixed
  let O := oddCore K
  let M := commutatorAction O V
  let _ : O.Normal := pPrimeCore_normal
  have hnorm : (⊤ : Subgroup K) ≤ Subgroup.normalizer (O : Set K) := by
    rw [Subgroup.normalizer_eq_top]
  have hinv := commutatorAction_isInvariant_of_normalizing_actor (V := V) (⊤ : Subgroup K) O hnorm
  let _ : IsInvariant K V M := ⟨fun k v => hinv.invariant ⟨k,Subgroup.mem_top k⟩ v⟩
  let _ : IsElementaryAbelian 2 M := elementary_subgroup M
  let f : K →* MulAut M := MulDistribMulAction.toMulAut K M
  have hkill : O ≤ f.ker := by
    rcases Theory.GroupTheory.wreathTwo_oddCore_le_ker_or_nine_dvd_range model f with hkill | hnine
    · exact hkill
    have hfaith : fixingSubgroup f.range (Set.univ : Set M) = ⊥ := by
      apply bot_unique
      intro a ha
      apply Subtype.ext
      ext m
      exact congrArg Subtype.val (((mem_fixingSubgroup_iff (M := f.range)
        (s := (Set.univ : Set M))).mp ha) m (Set.mem_univ m))
    have hlarge := faithful_binary_card_ge_sixteen_of_nine_dvd hfaith hnine
    change Nat.card M ≤ 4 at hsmall
    omega
  have hcop : Nat.Coprime (Nat.card O) (Nat.card V) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := K)).symm.pow_right n
  have hcompl := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := V) (A := O) (Group.isSolvable_of_comm fun v w => mul_comm v w) hcop inferInstance
  have hMF : M ≤ FixedPoints.subgroup O V := by
    intro m hm o
    have heq : f (o : K) = 1 := MonoidHom.mem_ker.mp (hkill o.property)
    exact congrArg Subtype.val (DFunLike.congr_fun heq (⟨m,hm⟩ : M))
  have hMbot : M = ⊥ := by
    apply bot_unique
    intro m hm
    exact hcompl.disjoint.le_bot ⟨hMF hm,hm⟩
  intro o ho v
  have hdelta : v⁻¹ * (o • v) ∈ M := by
    change v⁻¹ * (o • v) ∈ commutatorAction O V
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨o,ho⟩,v,rfl⟩
  have hone : v⁻¹ * (o • v) = 1 := hMbot.le hdelta
  exact (inv_mul_eq_one.mp hone).symm


public theorem wreath_action_image_isTwoGroup_of_fixed_coatom
    {K V : Type u} [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (model : Nonempty (K ≃* Stellmacher.Later.SL2TwoWreathC2))
    (S : Sylow 2 K) (A : Subgroup K) (hAS : A ≤ (S : Subgroup K))
    (hAN : (A.subgroupOf (S : Subgroup K)).Normal)
    (hAE : IsElementaryAbelian 2 A) (hAc : Nat.card A = 4)
    (C : Subgroup V) (hindex : C.index ≤ 2)
    (hfixed : ∀ a ∈ A, ∀ c ∈ C, a • c = c) :
    IsPGroup 2 (MulDistribMulAction.toMulAut K V).range := by
  let f := MulDistribMulAction.toMulAut K V
  have hkill := wreath_oddCore_fixes_of_fixed_coatom model S A hAS hAN hAE hAc C hindex hfixed
  have hker : oddCore K ≤ f.ker := by
    intro o ho
    rw [MonoidHom.mem_ker]
    ext v
    exact hkill o ho v
  have hOindex : (oddCore K).index = 8 :=
    Theory.GroupTheory.wreathTwo_oddCore_index_eight model
  have hdiv := Subgroup.index_dvd_of_le hker
  rw [Subgroup.index_ker,hOindex] at hdiv
  exact IsPGroup.of_card_dvd_pow (n := 3) hdiv

end Stellmacher.SectionOne
