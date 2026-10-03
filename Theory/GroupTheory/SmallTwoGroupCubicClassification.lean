module
public import Theory.GroupTheory.OrderEightCubicQuotientModel
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Small two-groups with a nontrivial cubic automorphism

A finite two-group of order at most eight admitting a nonidentity
automorphism whose cube is one is elementary abelian or isomorphic to
the quaternion group of order eight. No central subgroup, quotient model,
or faithfulness hypothesis is supplied by the caller.

Burnside's Frattini automorphism kernel is a two-group, so the given
cubic automorphism remains nonidentity on the elementary Frattini quotient.
A moved element has a three-element orbit disjoint from the identity;
therefore this quotient has at least four elements. If the original group
is not elementary, its Frattini subgroup has at least two elements.
The order bound forces orders eight, two, and four for the group,
Frattini subgroup, and quotient. The normal subgroup of order two is
central, and the existing cubic action recognition theorem for a central
Klein quotient gives the quaternion alternative.

This source-neutral fact supplies the small middle-core quotient
classification in Stellmacher (10.1), Journal of Algebra 190 (1997),
printed p.65. All quotient automorphisms are the canonical ones induced
from the supplied automorphism of the original group.
-/

private theorem card_ge_four_of_nontrivial_cubic_automorphism
    {W : Type*} [Group W] [Finite W]
    (b : MulAut W) (hb : b ^ 3 = 1) (hne : b ≠ 1) : 4 ≤ Nat.card W := by
  classical
  have h3 (w : W) : b (b (b w)) = w := by
    simpa only [pow_succ,pow_zero,one_mul,MulAut.mul_apply,MulAut.one_apply] using
      congrArg (fun f : MulAut W => f w) hb
  obtain ⟨w,hw⟩ : ∃ w : W, b w ≠ w := by
    by_contra! hh
    exact hne (MulEquiv.ext hh)
  have hw1 : w ≠ 1 := by intro hh; subst w; simp at hw
  have hbw1 : b w ≠ 1 := by simpa using hw1
  have hbbw1 : b (b w) ≠ 1 := by simpa using hw1
  have hww : b (b w) ≠ w := by
    intro hh
    exact hw ((congrArg b hh).symm.trans (h3 w))
  have hbw : b (b w) ≠ b w := fun hh => hw (b.injective hh)
  let _ : Fintype W := Fintype.ofFinite W
  have hfour : ({1,w,b w,b (b w)} : Finset W).card = 4 := by
    simp [Ne.symm hw1,Ne.symm hbw1,Ne.symm hbbw1,
      Ne.symm hw,Ne.symm hww,Ne.symm hbw]
  rw [←hfour,Nat.card_eq_fintype_card]
  exact Finset.card_le_univ _

public theorem elementary_or_quaternion_of_small_two_group_cubic
    {X : Type*} [Group X] [Finite X]
    (hX : IsPGroup 2 X) (hcard : Nat.card X ≤ 8)
    (a : MulAut X) (hcubic : a ^ 3 = 1) (hne : a ≠ 1) :
    IsElementaryAbelian 2 X ∨ Nonempty (X ≃* QuaternionGroup 2) := by
  classical
  let _ : Fact (IsPGroup 2 X) := ⟨hX⟩
  by_cases hel : IsElementaryAbelian 2 X
  · exact Or.inl hel
  let Z := frattini X
  let W := X ⧸ Z
  let b : MulAut W := Subgroup.quotientAut Z a
  let _ : IsElementaryAbelian 2 W := isElementaryAbelian_quotient_frattini
  have hb3 : b ^ 3 = 1 := by
    change (Subgroup.quotientAut Z a) ^ 3 = 1
    rw [←map_pow,hcubic,map_one]
  have hbne : b ≠ 1 := by
    intro hzero
    let K := (Subgroup.quotientAut (frattini X)).ker
    let x : K := ⟨a,hzero⟩
    have hK := Subgroup.isPGroup_quotientAut_frattini_kernel hX
    have hcop := hK.orderOf_coprime (by decide : Nat.Coprime 2 3) x
    have hdiv : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext hcubic)
    have hx : x = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hdiv)
    exact hne (congrArg Subtype.val hx)
  have hZne : Z ≠ ⊥ := fun hz =>
    hel ((frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hz)
  have hZlow : 2 ≤ Nat.card Z := by
    have hh := (Subgroup.one_lt_card_iff_ne_bot Z).mpr hZne
    omega
  have hWlow : 4 ≤ Nat.card W := card_ge_four_of_nontrivial_cubic_automorphism b hb3 hbne
  have hprod : Nat.card Z * Nat.card W = Nat.card X := Z.card_mul_index
  have hZcard : Nat.card Z = 2 := by
    have hh := (Nat.mul_le_mul_left (Nat.card Z) hWlow).trans (hprod.le.trans hcard)
    omega
  have hWcard : Nat.card W = 4 := by
    rw [hZcard] at hprod
    omega
  have hXcard : Nat.card X = 8 := by
    rw [hZcard,hWcard] at hprod
    omega
  exact elementary_or_quaternion_of_cubic_quotient_action hXcard Z hZcard
    (Subgroup.central_of_normal_card_two Z hZcard) hWcard a b
    (fun x => Subgroup.quotientAut_apply_mk Z a x) hb3 hbne
