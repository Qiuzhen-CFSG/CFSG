module

public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.GroupAction.QuotientConjugation
public import Theory.GroupTheory.Involution.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Small involutions above a self-centralizing cyclic prime subgroup

An elementary two-subgroup acting on a self-centralizing normal subgroup of
odd prime order embeds in its cyclic automorphism group. Thus every nontrivial
such actor has order two, and its involution inverts the prime subgroup.
The attained cubic ratio supplies one with fixed codimension at most two.

This is the local action step in Aschbacher–Smith 15.4.3(4), printed p.1157.
The small-support order bound is applied in the source consumer; no global
minimal cubic offender or general D.2.13 classification is used here.
-/

noncomputable section
open Subgroup BenderSuzuki.PFAppendixIII
namespace Representation.CyclicPrimeSmallRatio
open BinaryOffender
variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V]

omit [Finite D] in
private theorem conjugation_injective {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (P : Subgroup D) [P.Normal] (hP : Nat.card P = p)
    (hC : centralizer (P : Set D) ≤ P)
    (A : Subgroup D) (hA : IsElementaryTwo A) :
    Function.Injective ((MulAut.conjNormal : D →* MulAut P).comp A.subtype) := by
  let : IsElementaryAbelian 2 A := hA.2
  have hpp : IsPGroup p P := IsPGroup.of_card (n := 1) (by simpa using hP)
  have hd : Disjoint A P :=
    (IsElementaryAbelian.isPGroup 2 A).disjoint_of_coprime hpp hp.coprime_two_left
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hac : (a : D) ∈ centralizer (P : Set D) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer P]
    exact ha
  exact Subtype.ext (disjoint_def.mp hd a.property (hC hac))

omit [Finite D] in
/-- Every nontrivial elementary two-subgroup has order two. -/
public theorem elementary_card_two {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (P : Subgroup D) [P.Normal] (hP : Nat.card P = p)
    (hC : centralizer (P : Set D) ≤ P)
    (A : Subgroup D) (hA : IsElementaryTwo A) : Nat.card A = 2 := by
  let : IsElementaryAbelian 2 A := hA.2
  let : IsCyclic P := isCyclic_of_prime_card hP
  let e : MulAut P ≃* (ZMod p)ˣ := by
    have e := IsCyclic.mulAutMulEquiv P
    rw [hP] at e
    exact e
  let : IsCyclic (MulAut P) := isCyclic_of_injective e.toMonoidHom e.injective
  let : IsCyclic A := isCyclic_of_injective _ (conjugation_injective hp P hP hC A hA)
  have hd : Nat.card A ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 A
  exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
    (fun h => hA.1 ((eq_bot_iff_card A).mpr h))

private theorem inversion_on_prime {p : ℕ} [Fact p.Prime]
    (P : Subgroup D) [P.Normal] (hP : Nat.card P = p)
    (hC : centralizer (P : Set D) ≤ P)
    (t : D) (ht : BenderSuzuki.PFAppendixIII.IsInvolution t) (htP : t ∉ P) :
    ∀ x : P, t * (x : D) * t⁻¹ = (x : D)⁻¹ := by
  let φ : MulAut P := MulAut.conjNormal t
  have hf : MonoidHom.FixedPointFree φ := by
    intro x hx
    by_contra hne
    have hφ : φ = 1 := by
      ext y
      obtain ⟨n, hy⟩ := mem_zpowers_iff.mp
        (show y ∈ zpowers x from mem_zpowers_of_prime_card hP hne)
      rw [← hy]
      simp only [map_zpow, hx, MulAut.one_apply]
    apply htP
    apply hC
    rw [← MulAut.conjNormal_ker_eq_centralizer P]
    exact hφ
  have hi : Function.Involutive φ := by
    intro x
    have he := congrArg (fun a : MulAut P => a x)
      (show φ * φ = 1 by
        change MulAut.conjNormal t * MulAut.conjNormal t = 1
        rw [← map_mul, ← pow_two, ht.sq_eq_one, map_one])
    exact he
  intro x
  exact congrArg Subtype.val (congrFun (hf.coe_eq_inv_of_involutive hi) x)

/-- A finite cubic ratio at most two supplies an actual involution of support
at most two which inverts an element of the prescribed odd prime order. -/
public theorem exists_small_inverter {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (P : Subgroup D) [P.Normal] (hP : Nat.card P = p)
    (hC : centralizer (P : Set D) ≤ P)
    (ρ : Representation (ZMod 2) D V) (hq : cubicRatio ρ ≤ 2) :
    ∃ t x : D, BenderSuzuki.PFAppendixIII.IsInvolution t ∧ x ∈ P ∧ orderOf x = p ∧
      t * x * t⁻¹ = x⁻¹ ∧ fixedCodim ρ (zpowers t) ≤ 2 := by
  obtain ⟨A, hA, _, hb⟩ := (cubicRatio_le_nat_iff ρ 2).mp hq
  let : IsElementaryAbelian 2 A := hA.2
  let : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hA.1
  have hc := elementary_card_two hp P hP hC A hA
  obtain ⟨t, ht⟩ := exists_ne (1 : A)
  have htp : (t : D) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (t : D) t.property
  have ht1 : (t : D) ≠ 1 := fun h => ht (Subtype.ext h)
  have hti : BenderSuzuki.PFAppendixIII.IsInvolution (t : D) := ⟨ht1, htp⟩
  have htP : (t : D) ∉ P := by
    intro h
    have hd := (IsElementaryAbelian.isPGroup 2 A).disjoint_of_coprime
      (IsPGroup.of_card (n := 1) (show Nat.card P = p ^ 1 by simpa using hP))
      hp.coprime_two_left
    exact ht1 (disjoint_def.mp hd t.property h)
  have hgen : zpowers (t : D) = A := by
    apply le_antisymm (zpowers_le.mpr t.property)
    have hcard : Nat.card (zpowers (t : D)) = Nat.card A := by
      rw [Nat.card_zpowers, orderOf_eq_prime htp ht1, hc]
    exact (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr t.property) hcard.symm.le).ge
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p (show p ∣ Nat.card P by rw [hP])
  refine ⟨t, x, hti, x.property, (Subgroup.orderOf_coe x).trans hx,
    inversion_on_prime P hP hC t hti htP x, ?_⟩
  rw [hgen]
  norm_num [rank, hc] at hb ⊢
  exact hb

end Representation.CyclicPrimeSmallRatio
