module

public import Theory.GroupTheory.PGroup.UniqueInvolutionClassification
public import Theory.ElementaryAbelian.Basic

/-!
# Involutions above an elementary subgroup in a double cover

An extension with kernel of order two and elementary quotient of order greater
than four has an involution outside its kernel. Otherwise it has a unique
involution, so it is cyclic or generalized quaternion. Every element has fourth
power one, bounding its order by eight, contrary to the quotient order.
Surjectivity then lifts conjugators, propagating this involution to its entire
quotient conjugacy class. Centrality of the kernel is unnecessary for this step.

This is the elementary-subgroup case of observation (ii) in the proof of
Aschbacher–Smith I.2.2, combined 1 March 2004 manuscript, printed p.410.
The application to the actual long-root plane of G₂(4) is in
`Theory.SpecificGroups.G2.DoubleCoverInvolutions`.
-/

public section
namespace Theory.GroupTheory.DoubleCoverInvolutionLifting
open Subgroup

theorem exists_involution_above_elementary
    {P Q : Type*} [Group P] [Finite P] [Group Q] [Finite Q]
    [IsElementaryAbelian 2 Q] (f : P →* Q) (hf : Function.Surjective f)
    (hk : Nat.card f.ker = 2) (hQ : 4 < Nat.card Q) :
    ∃ x : P, orderOf x = 2 ∧ f x ≠ 1 := by
  have hpow (x : P) : x ^ 4 = 1 := by
    have hs : x ^ 2 ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 Q) _
    have hp := pow_card_eq_one' (x := (⟨x ^ 2, hs⟩ : f.ker))
    rw [hk] at hp
    have hh := congrArg Subtype.val hp
    change (x ^ 2) ^ 2 = 1 at hh
    simpa only [← pow_mul] using hh
  have hcard : Nat.card P = Nat.card Q * 2 := by
    have hi : f.ker.index = Nat.card Q := by
      rw [index_eq_card]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
    rw [← f.ker.index_mul_card, hi, hk]
  by_contra! hn
  obtain ⟨z, hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : f.ker)).mp hk
  have hz2 : orderOf z = 2 := by
    apply orderOf_eq_prime_iff.mpr
    exact ⟨by simpa only [hk] using (pow_card_eq_one' (x := z)), hz⟩
  have hunique : ∃! z : P, orderOf z = 2 := by
    refine ⟨z, (orderOf_injective f.ker.subtype f.ker.subtype_injective z).trans hz2, ?_⟩
    intro x hx
    have hxk : x ∈ f.ker := hn x hx
    have he : (⟨x, hxk⟩ : f.ker) = z := huniq _ (by
      intro he
      have hx1 : x = 1 := congrArg Subtype.val he
      simp [hx1] at hx)
    exact congrArg Subtype.val he
  have hp : IsPGroup 2 P := fun x => ⟨2, hpow x⟩
  rcases hp.isCyclic_or_quaternion_of_unique_involution hunique with hc | ⟨n, hn, ⟨e⟩⟩
  · let := hc
    have hd : Nat.card P ∣ 4 := by
      rw [← IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow
    have hh := Nat.le_of_dvd (by decide : 0 < 4) hd
    omega
  · have hd : 2 * 2 ^ (n - 2) ∣ 4 := by
      rw [← QuaternionGroup.orderOf_a_one]
      apply orderOf_dvd_of_pow_eq_one
      obtain ⟨x, hx⟩ := e.surjective (QuaternionGroup.a 1)
      rw [← hx, ← map_pow, hpow, map_one]
    have hh := Nat.le_of_dvd (by decide : 0 < 4) hd
    have hc : Nat.card P = 4 * 2 ^ (n - 2) := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    omega


theorem exists_involution_above_elementary_subgroup
    {P Q : Type*} [Group P] [Finite P] [Group Q] [Finite Q]
    (f : P →* Q) (hf : Function.Surjective f) (hk : Nat.card f.ker = 2)
    (E : Subgroup Q) [IsElementaryAbelian 2 E] (hE : 4 < Nat.card E) :
    ∃ x : P, orderOf x = 2 ∧ f x ∈ E ∧ f x ≠ 1 := by
  let D := E.comap f
  let r : D →* E := f.restrict (fun _ hx => hx)
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨⟨x, by change f x ∈ E; rw [hx]; exact y.property⟩, Subtype.ext hx⟩
  have hle : f.ker ≤ D := by
    intro x hx
    change f x ∈ E
    rw [show f x = 1 from hx]
    exact E.one_mem
  have he : r.ker = f.ker.subgroupOf D := by
    ext x
    change (⟨f x, x.property⟩ : E) = 1 ↔ f x = 1
    exact Subtype.ext_iff
  have hc : Nat.card r.ker = 2 := by
    rw [he, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, hk]
  obtain ⟨x, hx, hxn⟩ := exists_involution_above_elementary r hr hc hE
  exact ⟨x, (orderOf_injective D.subtype D.subtype_injective x).trans hx,
    x.property, fun hh => hxn (Subtype.ext hh)⟩

theorem involution_lift_of_isConj
    {P Q : Type*} [Group P] [Group Q]
    (f : P →* Q) (hf : Function.Surjective f) {x : P} (hx : orderOf x = 2)
    {y : Q} (hy : IsConj (f x) y) :
    ∃ z : P, f z = y ∧ orderOf z = 2 := by
  obtain ⟨a, ha⟩ := isConj_iff.mp hy
  obtain ⟨b, rfl⟩ := hf a
  refine ⟨MulAut.conj b x, ?_, (MulAut.conj b).orderOf_eq x |>.trans hx⟩
  simpa only [MulAut.conj_apply, map_mul, map_inv] using ha


end Theory.GroupTheory.DoubleCoverInvolutionLifting
