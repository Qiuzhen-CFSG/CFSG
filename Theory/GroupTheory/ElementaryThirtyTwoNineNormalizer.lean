module

public import Theory.GroupTheory.ElementaryThirtyTwoThreeSubgroups
public import Theory.GroupAction.CoprimeNormalizerDecomposition
public import Theory.GroupAction.OddInvolutionFixedFaithful

/-!
# Order-nine normalizers on an elementary thirty-two

An order-nine subgroup A of the automorphism group of an elementary abelian
two-group E of order thirty-two has normalizer order not divisible by 64.
Coprime splitting gives a fixed line and a moving summand of order sixteen;
the normalizer acts faithfully on the latter, since the line has no
nonidentity automorphisms.

The centralizer of the restricted order-nine subgroup has odd order. Indeed,
an involution in that centralizer would make the odd actor act faithfully
on its proper fixed subgroup, of order at most eight. The automorphism
orders of these smaller binary groups are not divisible by nine. Conjugation
on A then bounds the normalizer modulo its odd centralizer by Aut(A),
whose order divides 48 for every group of order nine.

This proves the divisibility obstruction needed from Parrott,
"A Characterization of the Tits' Simple Group" (1972), printed p.673,
property (4), without using the classification of the normalizer.
-/

open Subgroup
open scoped IsMulCommutative

private instance elementary_subgroup
    {E : Type*} [Group E] [IsElementaryAbelian 2 E] (D : Subgroup E) :
    IsElementaryAbelian 2 D where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom D.subtype D.subtype_injective).trans
    (IsElementaryAbelian.exponent_dvd_p 2 E)

private theorem odd_centralizer_sixteen_nine
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (A : Subgroup (MulAut V)) (hA : Nat.card A = 9) :
    Odd (Nat.card (centralizer (A : Set (MulAut V)))) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  let C := centralizer (A : Set (MulAut V))
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (even_iff_two_dvd.mp heven)
  let t : MulAut V := c
  have ht : orderOf t = 2 := (orderOf_injective C.subtype C.subtype_injective c).trans hc
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  let Q := zpowers t
  have hQA : Q ≤ centralizer (A : Set (MulAut V)) := zpowers_le.mpr c.property
  have hAQ : A ≤ centralizer (Q : Set (MulAut V)) := le_centralizer_iff.mp hQA
  let F := FixedPoints.subgroup Q V
  let : IsInvariant A V F := fixedPoints_isInvariant_of_normalizing_actor A Q
    (hAQ.trans (centralizer_le_normalizer _))
  have hfaith := MulAut.odd_centralizer_fixed_action_faithful t ht2 A
    (by rw [hA]; decide) hAQ
  let f := MulDistribMulAction.toMulAut A F
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    apply hfaith.le
    rw [mem_fixingSubgroup_iff]
    intro v hv
    exact congrArg Subtype.val (MulEquiv.congr_fun (MonoidHom.mem_ker.mp ha) ⟨v, hv⟩)
  have hdiv : 9 ∣ Nat.card (MulAut F) := hA ▸ card_dvd_of_injective f hf
  have hproper : Nat.card F ≠ 16 := by
    intro hh
    have htop : F = ⊤ := F.eq_top_of_card_eq (hh.trans hV.symm)
    have htone : t = 1 := by
      apply MulEquiv.ext
      intro v
      have hv : v ∈ F := htop ▸ mem_top v
      exact hv ⟨t, mem_zpowers t⟩
    rw [htone, orderOf_one] at ht
    omega
  have hFdiv : Nat.card F ∣ 2 ^ 4 := by
    simpa [hV] using F.card_subgroup_dvd_card
  obtain ⟨n, hn, hncard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hFdiv
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow F n hncard] at hdiv
  interval_cases n <;> norm_num [Fin.prod_univ_succ] at hdiv
  exact hproper hncard

private theorem card_aut_nine_dvd_fortyeight
    {A : Type*} [Group A] [Finite A] (hA : Nat.card A = 9) :
    Nat.card (MulAut A) ∣ 48 := by
  classical
  by_cases hcyc : IsCyclic A
  · let : IsCyclic A := hcyc
    rw [IsCyclic.card_mulAut, hA]
    decide
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsMulCommutative A := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hA
  let : IsElementaryAbelian 3 A :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := ((not_isCyclic_iff_exponent_eq_prime Nat.prime_three hA).mp hcyc) ▸ dvd_rfl }
  have hpow : 3 ^ Module.finrank (ZMod 3) (Additive A) = 3 ^ 2 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive A)
    change Nat.card A = _ at hsize
    simpa [Nat.card_zmod, hA] using hsize.symm
  have hdim : Module.finrank (ZMod 3) (Additive A) = 2 :=
    Nat.pow_right_injective (by decide : 1 < 3) hpow
  let autLinear : MulAut A ≃* (Additive A ≃ₗ[ZMod 3] Additive A) :=
    { toFun := fun aut =>
        { aut.toAdditive with map_smul' := ZMod.map_smul aut.toAdditive }
      invFun := fun aut => MulEquiv.toAdditive.symm aut.toAddEquiv
      left_inv := by intro aut; ext; rfl
      right_inv := by intro aut; ext; rfl
      map_mul' := by intro aut other; ext; rfl }
  let basis := Module.finBasisOfFinrankEq (ZMod 3) (Additive A) hdim
  let coordinates := autLinear.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Additive A)).symm.trans
      (Matrix.GeneralLinearGroup.toLin' basis).symm)
  rw [Nat.card_congr coordinates.toEquiv, Matrix.card_GL_field]
  norm_num [ZMod.card, Fin.prod_univ_succ]

private theorem not_sixtyfour_normalizer_sixteen_nine
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (A : Subgroup (MulAut V)) (hA : Nat.card A = 9) :
    ¬ 64 ∣ Nat.card (normalizer (A : Set (MulAut V))) := by
  let f := A.normalizerMonoidHom
  have hrange : Nat.card f.range ∣ 48 :=
    f.range.card_subgroup_dvd_card.trans (card_aut_nine_dvd_fortyeight hA)
  have hker : Odd (Nat.card f.ker) := by
    have hc := odd_centralizer_sixteen_nine hV A hA
    have heq : Nat.card f.ker = Nat.card (centralizer (A : Set (MulAut V))) := by
      rw [normalizerMonoidHom_ker,
        Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (A : Set (MulAut V)))).toEquiv]
    rwa [heq]
  have hprod := f.ker.card_mul_index
  rw [index_ker] at hprod
  intro h64
  have hdiv : 64 ∣ Nat.card f.range := by
    apply (hker.coprime_two_left.pow_left 6).dvd_of_dvd_mul_left
    simpa only [hprod] using h64
  have := hdiv.trans hrange
  norm_num at this

/-- The normalizer of an order-nine subgroup of Aut(E), for elementary E of
order thirty-two, has order not divisible by sixty-four. -/
public theorem not_sixtyfour_dvd_card_normalizer_of_elementary_thirtytwo_nine
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (A : Subgroup (MulAut E)) (hA : Nat.card A = 9) :
    ¬ 64 ∣ Nat.card (normalizer (A : Set (MulAut E))) := by
  obtain ⟨hF, hC⟩ := fixed_and_commutator_card_of_elementary_thirtytwo_nine hE A hA
  have hcop : Nat.Coprime (Nat.card A) (Nat.card E) := by rw [hA, hE]; decide
  have hAut : Nat.card (MulAut (FixedPoints.subgroup A E)) = 1 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 1 (by simpa using hF)]
    decide
  obtain ⟨D, hD, hdiv⟩ := exists_restricted_coprime_normalizer A hcop
  rw [hAut, one_mul] at hdiv
  intro h64
  exact not_sixtyfour_normalizer_sixteen_nine hC D (hD.trans hA) (h64.trans hdiv)
