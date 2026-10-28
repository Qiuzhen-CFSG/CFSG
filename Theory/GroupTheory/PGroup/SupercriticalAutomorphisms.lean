module

public import Theory.GroupTheory.PGroup.Supercritical
public import Theory.GroupTheory.PGroup.OddOmegaAutomorphisms
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
import Mathlib.Tactic.Group

/-!
# Supercritical subgroups detect coprime automorphisms

The kernel of Aut(P) → Aut(X/Φ(X)) is a p-group when X is supercritical
in a finite odd p-group P. An automorphism fixing X displaces every element
of P into C = C_P(X). The order-p condition on C and odd-prime omega
detection force every coprime such automorphism to fix C. It also acts
trivially on P/C, so the paired automorphism kernel forces it to be trivial.
Finally the Burnside basis kernel theorem handles passage from X to X/Φ(X).

The argument uses the actual supercritical centralizer condition, without
assuming that C lies in X. It applies to any supplied supercritical subgroup
and does not depend on existence of one. The resulting kernel theorem gives
faithfulness for every finite faithful p'-actor, in particular each cyclic
p'-automorphism group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Definition A.1.20 and Lemma A.1.21(3), printed pp.24–25.
-/

open Subgroup
namespace IsSupercriticalPSubgroup
variable {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
  {X : Subgroup P}

omit [Fact p.Prime] [Finite P] in
private theorem displacement_mem_centralizer (hX : IsSupercriticalPSubgroup p X)
    (a : MulAut P) (hfix : ∀ x ∈ X, a x = x) (g : P) :
    g⁻¹ * a g ∈ centralizer (X : Set P) := by
  let : X.Characteristic := hX.characteristic
  intro x hx
  have h := hfix (g * x * g⁻¹) ((inferInstance : X.Normal).conj_mem x hx g)
  simp only [map_mul, map_inv, hfix x hx] at h
  have hh := congrArg (fun t : P => g⁻¹ * t * a g) h
  group at hh
  simpa only [mul_assoc, zpow_neg_one] using hh.symm

/-- Automorphisms fixing a supercritical subgroup pointwise form a p-group. -/
public theorem isPGroup_restriction_kernel (hX : IsSupercriticalPSubgroup p X)
    (hP : IsPGroup p P) (hp : Odd p) :
    letI : X.Characteristic := hX.characteristic
    IsPGroup p (MulAut.characteristic X).ker := by
  let : X.Characteristic := hX.characteristic
  let C := centralizer (X : Set P)
  let K := (MulAut.characteristic X).ker
  have hp2 : p ≠ 2 := by rintro rfl; obtain ⟨k, hk⟩ := hp; omega
  apply isPGroup_of_prime_order_eq_p p K
  intro a ha
  by_contra hne
  have hcop : p.Coprime (orderOf (a : MulAut P)) := by
    rw [orderOf_coe]
    exact (Nat.coprime_primes (Fact.out : p.Prime) ha).mpr (Ne.symm hne)
  have hfix (x : P) (hx : x ∈ X) : (a : MulAut P) x = x :=
    congrArg Subtype.val (DFunLike.congr_fun a.property (⟨x, hx⟩ : X))
  have hCfix : MulAut.characteristic C (a : MulAut P) = 1 := by
    apply MulAut.eq_one_of_coprime_of_fixes_prime_roots (hP.to_subgroup C) hp2
    · exact hcop.of_dvd_right (orderOf_map_dvd (MulAut.characteristic C) a)
    · intro x hx
      apply Subtype.ext
      apply hfix
      by_cases he : (x : P) = 1
      · exact he ▸ X.one_mem
      · exact hX.order_p_mem x x.property
          (orderOf_eq_prime_iff.mpr ⟨congrArg Subtype.val hx, he⟩)
  have hquot : quotientAut C (a : MulAut P) = 1 := by
    ext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C q
    rw [quotientAut_apply_mk]
    exact (QuotientGroup.eq.mpr (hX.displacement_mem_centralizer a hfix g)).symm
  have hpair : automorphismPair C (a : MulAut P) = 1 := by
    rw [automorphismPair_apply, hCfix, hquot]
    rfl
  have ho := (automorphismPair C).orderOf_map_eq_of_coprime_of_isPGroup_ker
    (isPGroup_automorphism_pair_kernel C (hP.to_subgroup C)) a hcop
  rw [hpair, orderOf_one, orderOf_coe] at ho
  exact ha.ne_one ho.symm

/-- The action on the supercritical Frattini quotient has p-group kernel. -/
public theorem isPGroup_frattini_action_kernel (hX : IsSupercriticalPSubgroup p X)
    (hP : IsPGroup p P) (hp : Odd p) :
    letI : X.Characteristic := hX.characteristic
    IsPGroup p ((quotientAut (frattini X)).comp (MulAut.characteristic X)).ker := by
  let : X.Characteristic := hX.characteristic
  exact (isPGroup_quotientAut_frattini_kernel (hP.to_subgroup X)).comap_of_ker_isPGroup
    (MulAut.characteristic X) (hX.isPGroup_restriction_kernel hP hp)

/-- Restriction to X/Φ(X) preserves the order of every p'-automorphism. -/
public theorem orderOf_frattini_action_eq_of_coprime (hX : IsSupercriticalPSubgroup p X)
    (hP : IsPGroup p P) (hp : Odd p) (a : MulAut P)
    (hcop : p.Coprime (orderOf a)) :
    letI : X.Characteristic := hX.characteristic
    orderOf (quotientAut (frattini X) (MulAut.characteristic X a)) = orderOf a := by
  let : X.Characteristic := hX.characteristic
  exact ((quotientAut (frattini X)).comp (MulAut.characteristic X)).orderOf_map_eq_of_coprime_of_isPGroup_ker (hX.isPGroup_frattini_action_kernel hP hp) a hcop

/-- Every faithful finite p'-action remains faithful on X/Φ(X). -/
public theorem injective_frattini_action_of_coprime (hX : IsSupercriticalPSubgroup p X)
    (hP : IsPGroup p P) (hp : Odd p) {A : Type*} [Group A] [Finite A]
    (action : A →* MulAut P) (hfaith : Function.Injective action)
    (hcop : Nat.Coprime (Nat.card A) p) :
    letI : X.Characteristic := hX.characteristic
    Function.Injective
      (((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp action) := by
  let : X.Characteristic := hX.characteristic
  let f := ((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp action
  have hker : IsPGroup p f.ker :=
    (hX.isPGroup_frattini_action_kernel hP hp).comap_of_injective action hfaith
  obtain ⟨n, hn⟩ := hker.exists_card_dvd_pow
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply Subgroup.card_eq_one.mp
  exact Nat.eq_one_of_dvd_coprimes (hcop.pow_right n)
    f.ker.card_subgroup_dvd_card hn

/-- Each cyclic p'-automorphism group acts faithfully on X/Φ(X). -/
public theorem injective_cyclic_frattini_action_of_coprime (hX : IsSupercriticalPSubgroup p X)
    (hP : IsPGroup p P) (hp : Odd p) (a : MulAut P)
    (hcop : p.Coprime (orderOf a)) :
    letI : X.Characteristic := hX.characteristic
    Function.Injective (((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp
      (zpowers a).subtype) := by
  let : X.Characteristic := hX.characteristic
  exact hX.injective_frattini_action_of_coprime hP hp (zpowers a).subtype
    (zpowers a).subtype_injective (by simpa only [Nat.card_zpowers] using hcop.symm)

end IsSupercriticalPSubgroup
