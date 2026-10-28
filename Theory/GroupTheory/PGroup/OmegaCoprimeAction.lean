module

public import Theory.GroupTheory.PGroup.OmegaAction
public import Theory.GroupTheory.PCoreCharacteristicCentralizer
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.PrimeOrder

/-!
# Detecting coprime actions on the first omega subgroup

A coprime action on an abelian p-group is trivial if it fixes Ω₁: every
prime-order element has order p, so the coprime fixed-point theorem applies.
Applying this to cyclic actors proves that restriction to Ω₁ has p-group
kernel. Thus Ω₁ of an abelian self-centralizing p-core detects its ambient
centralizer. A coprime prime-group action fixing Ω₁ then fixes the whole
ambient group, using the characteristic restriction kernel theorem.

This is the higher-exponent replacement for the full-radical equality used
in Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of Proposition 1.3.8, printed p.513.
No exponent-p assumption or center–Frattini equality is used.
-/

open Subgroup
open scoped IsMulCommutative
namespace OmegaAction

/-- A coprime action fixing Ω₁ of an abelian p-group is trivial. -/
public theorem fixes_of_fixes_omega_one {A Q : Type*} [Group A] [Finite A]
    [Group Q] [Finite Q] [IsMulCommutative Q] {p : ℕ} [Fact p.Prime]
    (hQ : IsPGroup p Q) (ρ : A →* MulAut Q)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card Q))
    (hfix : ∀ a : A, ∀ x ∈ omega Q (p := p) 1, ρ a x = x) :
    ∀ a : A, ρ a = 1 := by
  let := MulDistribMulAction.compHom Q ρ
  have hsolv : Group.IsSolvable Q := Group.isSolvable_of_comm (fun a b => mul_comm a b)
  have ht := actsTrivially_of_isMulCommutative_and_prime_order_mem_fixedPointSubgroup
    (G := Q) (A := A) hsolv hcop inferInstance ?_
  · intro a
    apply MulEquiv.ext
    intro x
    exact ht a x
  · intro x hx
    obtain ⟨n, hn⟩ := hQ x
    have hd : orderOf x ∣ p := hx.dvd_of_dvd_pow (orderOf_dvd_of_pow_eq_one hn)
    have he : orderOf x = p := ((Nat.dvd_prime (Fact.out : p.Prime)).mp hd).resolve_left hx.ne_one
    have hω : x ∈ omega Q (p := p) 1 := subset_closure (by
      change x ^ (p ^ 1) = 1
      simpa only [pow_one, ← he] using pow_orderOf_eq_one x)
    intro a
    exact hfix a x hω

/-- Restriction to Ω₁ of a finite abelian p-group has p-group kernel. -/
public theorem restriction_kernel_isPGroup {Q : Type*} [Group Q] [Finite Q]
    [IsMulCommutative Q] {p : ℕ} [Fact p.Prime] (hQ : IsPGroup p Q) :
    IsPGroup p (omegaRestriction Q p 1).ker := by
  let K := (omegaRestriction Q p 1).ker
  apply isPGroup_of_prime_order_eq_p p K
  intro a ha
  by_contra hne
  let ρ : zpowers a →* MulAut Q := K.subtype.comp (zpowers a).subtype
  have hc : Nat.Coprime (Nat.card (zpowers a)) (Nat.card Q) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp hQ
    rw [Nat.card_zpowers, hn]
    exact ((Nat.coprime_primes ha (Fact.out : p.Prime)).mpr hne).pow_right n
  have ht := fixes_of_fixes_omega_one hQ ρ hc (by
    intro b x hx
    exact congrArg (fun f : MulAut (omega Q (p := p) 1) => (f ⟨x, hx⟩ : Q)) b.val.property)
  have ha1 : a = 1 := Subtype.ext (ht ⟨a, mem_zpowers a⟩)
  have := ha.ne_one
  simp only [ha1, orderOf_one] at this
  exact this rfl


/-- The first omega subgroup detects the centralizer of an abelian p-core. -/
public theorem centralizer_omegaOne_pCore_le {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] [IsMulCommutative (pCore p G)]
    (hcentral : centralizer (pCore p G : Set G) ≤ pCore p G) :
    centralizer ((omega (pCore p G) (p := p) 1).map (pCore p G).subtype : Set G) ≤
      pCore p G := by
  let := omega_characteristic (pCore p G) (p := p) 1
  exact centralizer_le_pCore_of_characteristic_detection p hcentral _
    (restriction_kernel_isPGroup pCore_isPGroup)

end OmegaAction

namespace Subgroup

/-- A coprime prime-group action fixing a self-centralizing characteristic
p-subgroup is trivial. The subgroup need not be abelian. -/
public theorem action_eq_one_of_fixes_selfCentralizing
    {G A : Type*} [Group G] [Finite G] [Group A] {p q : ℕ}
    (Q : Subgroup G) [Q.Characteristic]
    (hQ : IsPGroup p Q) (hA : IsPGroup q A) (hcop : Nat.Coprime p q)
    (hcentral : centralizer (Q : Set G) ≤ Q) (ρ : A →* MulAut G)
    (hfix : ∀ a, MulAut.characteristic Q (ρ a) = 1) : ∀ a, ρ a = 1 := by
  have hd := (Q.isPGroup_characteristic_restriction_kernel_of_centralizer_le
    hQ hcentral).disjoint_of_coprime
      (hA.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective) hcop
  intro a
  exact disjoint_def.mp hd (hfix a) ⟨a, rfl⟩

end Subgroup

namespace OmegaAction

/-- A coprime prime-group action on a finite group is detected on Ω₁ of
an abelian self-centralizing characteristic p-subgroup. -/
public theorem action_eq_one_of_fixes_omegaOne_selfCentralizing
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (Q : Subgroup G) [Q.Characteristic] [IsMulCommutative Q]
    (hQ : IsPGroup p Q) (hA : IsPGroup q A) (hpq : p ≠ q)
    (hcentral : centralizer (Q : Set G) ≤ Q) (ρ : A →* MulAut G)
    (hfix : ∀ a : A, ∀ x ∈ omega Q (p := p) 1, ρ a (x : G) = x) :
    ∀ a, ρ a = 1 := by
  have hc : Nat.Coprime (Nat.card A) (Nat.card Q) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp hQ
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := q)).mp hA
    rw [hn, hm]
    exact Nat.coprime_pow_primes _ _ (Fact.out : q.Prime) (Fact.out : p.Prime) hpq.symm
  have ht := fixes_of_fixes_omega_one hQ ((MulAut.characteristic Q).comp ρ) hc (by
    intro a x hx
    exact Subtype.ext (hfix a x hx))
  exact action_eq_one_of_fixes_selfCentralizing Q hQ hA
    ((Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr hpq)
    hcentral ρ ht

end OmegaAction
