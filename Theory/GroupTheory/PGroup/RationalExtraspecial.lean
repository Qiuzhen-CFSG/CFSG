module

public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupTheory.CentralCoprimePrimeLift
public import Theory.GroupTheory.CentralCoprimeCardLift

/-!
# Rational fusion in extraspecial prime subgroups

The configuration consists of an extraspecial subgroup of order p³ and a
nonidentity central element conjugate to all of its nonidentity powers in
the ambient group. Its faithful characteristic-two representations have
degree at least p(p−1); the representation argument is developed separately.

A central extension of order prime to p preserves this configuration. The
canonical Sylow lift gives an isomorphic subgroup, and uniqueness of
coprime torsion lifts preserves each literal conjugacy equation.

This is the central-cover transport needed for the odd PSU₃ degree minimum
used in Guralnick–Malle, Classification of 2F-modules I, Proposition 4.3,
and Aschbacher–Smith K.2, printed p.453. It does not assert existence of the
configuration in a unitary model or a bound on its Schur multiplier.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- An order-p³ extraspecial subgroup with a nonidentity central element
conjugate in the ambient group to each of its nonidentity powers. -/
@[expose] def HasRationalExtraspecialSubgroup (G : Type*) [Group G] (p : ℕ) : Prop :=
  ∃ P : Subgroup G, IsExtraspecial p P ∧ Nat.card P = p ^ 3 ∧
    ∃ z : P, z ∈ center P ∧ z ≠ 1 ∧
      ∀ i : ℕ, 0 < i → i < p → ∃ g : G, g * (z : G) * g⁻¹ = (z : G) ^ i

/-- The local configuration lifts through any central kernel of order prime
to p; the conjugacy equations lift by uniqueness of coprime torsion lifts. -/
theorem HasRationalExtraspecialSubgroup.of_central_coprime
    {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center G) (hcop : Nat.Coprime p (Nat.card f.ker))
    (h : HasRationalExtraspecialSubgroup H p) :
    HasRationalExtraspecialSubgroup G p := by
  obtain ⟨P, hP, hcard, z, hz, hz1, hconj⟩ := h
  let : IsExtraspecial p P := hP
  obtain ⟨A, _, hmap, _, _, hi⟩ := exists_prime_lift_of_central_coprime
    f hf hcentral hcop P (IsExtraspecial.isPGroup p P)
  let r : A →* P := (f.comp A.subtype).codRestrict P (fun a =>
    hmap ▸ mem_map_of_mem f a.property)
  have hr : Function.Bijective r := by
    constructor
    · intro a b hab
      exact hi (congrArg Subtype.val hab)
    · intro b
      have hb : (b : H) ∈ A.map f := hmap.symm ▸ b.property
      obtain ⟨a, ha, hab⟩ := hb
      exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  let e : A ≃* P := MulEquiv.ofBijective r hr
  have he (a : A) : (e a : H) = f a := rfl
  let a : A := e.symm z
  have haz : e a = z := e.apply_symm_apply z
  have ha : a ∈ center A := by
    apply mem_center_iff.mpr
    intro b
    apply e.injective
    simpa only [map_mul, haz] using mem_center_iff.mp hz (e b)
  have ha1 : a ≠ 1 := by
    intro hh
    apply hz1
    rw [← haz, hh, map_one]
  have hap : (a : G) ^ p = 1 := by
    have hh : a ^ p = 1 := by
      apply e.injective
      rw [map_pow, haz, map_one]
      have hzpow := pow_card_eq_one' (x := (⟨z, hz⟩ : center P))
      rw [IsExtraspecial.center_order_p p P] at hzpow
      exact congrArg Subtype.val hzpow
    exact congrArg Subtype.val hh
  refine ⟨A, IsExtraspecial.of_mulEquiv e.symm hP,
    (Nat.card_congr e.toEquiv).trans hcard, a, ha, ha1, ?_⟩
  intro i hi0 hip
  obtain ⟨g, hg⟩ := hconj i hi0 hip
  obtain ⟨c, hc⟩ := hf g
  refine ⟨c, f.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker hcentral hcop.symm ?_ ?_ ?_⟩
  · have hfa : f a = (z : H) := (he a).symm.trans (congrArg Subtype.val haz)
    simpa only [map_mul, map_inv, map_pow, hc, hfa] using hg
  · rw [conj_pow, hap]
    simp
  · rw [← pow_mul, Nat.mul_comm i p, pow_mul, hap, one_pow]

end Theory.GroupTheory
