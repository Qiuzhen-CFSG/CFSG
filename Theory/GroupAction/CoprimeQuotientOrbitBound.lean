module

public import Theory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.Data.Fintype.Card

/-!
# A coprime quotient orbit bound

Suppose a finite group acts coprimely on a finite solvable group `P`, and
all fixed points of every nonidentity actor lie in an invariant normal
subgroup `R`. Fixed-point lifting for each cyclic actor subgroup shows
that the action on `P/R` is free away from the identity. If `R` is proper,
one such orbit and the identity give `|B| < |P/R|`.

This counting step can be applied directly to the normal closure in GLS,
Volume 4, Chapter 2, Lemma 15.7, without identifying the intermediate
normalizer used in Lemma 15.6.
-/

open Subgroup

namespace Theory.GroupAction

/-- Coprime fixed-point lifting gives a free action away from the identity
on the quotient when all nontrivial-actor fixed points lie in the kernel. -/
public theorem fixed_quotient_eq_one_of_fixed_le
    {P B : Type*} [Group P] [Group B] [Finite P] [Finite B]
    [MulDistribMulAction B P] (R : Subgroup P) [R.Normal]
    (hR : IsInvariant B P R) (hsolv : Group.IsSolvable P)
    (hcop : Nat.Coprime (Nat.card B) (Nat.card P))
    (hfixed : ∀ b : B, b ≠ 1 → ∀ x : P, b • x = x → x ∈ R) :
    letI : MulDistribMulAction B (P ⧸ R) := quotientMulDistribMulAction R hR
    ∀ b : B, b ≠ 1 → ∀ x : P ⧸ R, b • x = x → x = 1 := by
  let : MulDistribMulAction B (P ⧸ R) := quotientMulDistribMulAction R hR
  intro b hb x hx
  let C := zpowers b
  let : MulDistribMulAction C P := MulDistribMulAction.compHom P C.subtype
  have hRC : IsInvariant C P R := ⟨fun c y => hR.invariant (c : B) y⟩
  have hcopC : Nat.Coprime (Nat.card C) (Nat.card P) :=
    hcop.of_dvd_left C.card_subgroup_dvd_card
  have hmap := fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime
    (A := C) hsolv hcopC R hRC
  have hxC : x ∈ @FixedPoints.subgroup C (P ⧸ R) _ _
      (quotientMulDistribMulAction R hRC) := by
    apply (FixedPoints.mem_subgroup _ _ _).mpr
    intro c
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp c.property
    have hh : (b ^ i) • x = x := MulAction.mem_fixedBy_zpow hx i
    change (c : B) • x = x
    rwa [hi] at hh
  rw [hmap] at hxC
  obtain ⟨y, hy, rfl⟩ := hxC
  apply (QuotientGroup.eq_one_iff y).mpr
  apply hfixed b hb y
  exact (FixedPoints.mem_subgroup _ _ _).mp hy ⟨b, mem_zpowers b⟩

/-- A nontrivial quotient with this coprime action has more elements than
the acting group. -/
public theorem card_actor_lt_card_quotient_of_fixed_le
    {P B : Type*} [Group P] [Group B] [Finite P] [Finite B]
    [MulDistribMulAction B P] (R : Subgroup P) [R.Normal]
    (hR : IsInvariant B P R) (hsolv : Group.IsSolvable P)
    (hcop : Nat.Coprime (Nat.card B) (Nat.card P)) (hproper : R ≠ ⊤)
    (hfixed : ∀ b : B, b ≠ 1 → ∀ x : P, b • x = x → x ∈ R) :
    Nat.card B < Nat.card (P ⧸ R) := by
  classical
  let : MulDistribMulAction B (P ⧸ R) := quotientMulDistribMulAction R hR
  let : Nontrivial (P ⧸ R) := QuotientGroup.nontrivial_iff.mpr hproper
  let : Fintype B := Fintype.ofFinite B
  let : Fintype (P ⧸ R) := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := exists_ne (1 : P ⧸ R)
  have hi : Function.Injective (fun b : B => b • x) := by
    intro b c heq
    change b • x = c • x at heq
    have he : (c⁻¹ * b) • x = x := by rw [mul_smul, heq, inv_smul_smul]
    have hcb : c⁻¹ * b = 1 := by
      by_contra hne
      exact hx (fixed_quotient_eq_one_of_fixed_le R hR hsolv hcop hfixed _ hne _ he)
    exact (inv_mul_eq_one.mp hcb).symm
  have hmiss : (1 : P ⧸ R) ∉ Set.range (fun b : B => b • x) := by
    rintro ⟨b, hb⟩
    exact hx ((MulDistribMulAction.toMulEquiv (P ⧸ R) b).injective
      (hb.trans (smul_one b).symm))
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_injective_of_notMem _ hi hmiss

end Theory.GroupAction
