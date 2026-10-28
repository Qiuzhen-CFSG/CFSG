module

public import Theory.GroupTheory.NoninvolutionBase
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card

/-!
# A centralizer bound excludes squares in an index-two coset

Let a finite group have order `2q³`, a normal subgroup `R` have order `2q²`,
and a normal subgroup `B ≤ R` have relative index two. If an element `u` of
`R ∖ B` has centralizer of order at most `2q`, orbit-stabilizer forces its
conjugacy class to exhaust `R ∖ B`. If that centralizer has exponent two,
none of these conjugates is a square.

This counting route supplies the fusion and nonsquareness step of GLS,
Volume 4, Chapter 2, Lemma 15.7 (`refs/KGroup/GLS4/Chapter2.tex`), using the
actual normal closure from Lemma 15.6. No fusion premise is assumed.
-/

open Subgroup
namespace Subgroup

/-- A sufficiently small involution centralizer forces fusion of the outside
coset; an exponent-two centralizer then excludes square roots. -/
public theorem squares_mem_of_index_two_of_centralizer_bound
    {H : Type*} [Group H] [Finite H] (R B : Subgroup H)
    [R.Normal] [B.Normal] (hBR : B ≤ R) (hi : B.relIndex R = 2)
    {q : ℕ} (hq : 0 < q) (hR : Nat.card R = 2 * q ^ 2)
    (hH : Nat.card H = 2 * q ^ 3) (u : H) (huR : u ∈ R) (huB : u ∉ B)
    (hc : Nat.card (centralizer ({u} : Set H)) ≤ 2 * q)
    (hsq : ∀ x ∈ centralizer ({u} : Set H), x ^ 2 = 1) :
    ∀ x : H, x ^ 2 ∈ R → x ^ 2 ∈ B := by
  classical
  let O := MulAction.orbit (ConjAct H) u
  have hO : O ⊆ (R : Set H) \ (B : Set H) := by
    rintro y ⟨g, rfl⟩
    change g.ofConjAct * u * g.ofConjAct⁻¹ ∈ R ∧
      g.ofConjAct * u * g.ofConjAct⁻¹ ∉ B
    refine ⟨(inferInstance : R.Normal).conj_mem u huR _, ?_⟩
    intro hh
    exact huB ((mem_normalizer_iff.mp
      (show g.ofConjAct ∈ normalizer (B : Set H) from le_normalizer_of_normal (mem_top _)) u).mpr hh)
  have hBc : Nat.card B = q ^ 2 := by
    have hcB := (B.subgroupOf R).card_mul_index
    have hh : Nat.card (B.subgroupOf R) = Nat.card B :=
      Nat.card_congr (subgroupOfEquivOfLe hBR).toEquiv
    rw [hh, show (B.subgroupOf R).index = 2 from hi, hR] at hcB
    omega
  have hdiff : ((R : Set H) \ (B : Set H)).ncard = q ^ 2 := by
    rw [Set.ncard_sdiff hBR]
    change Nat.card R - Nat.card B = q ^ 2
    rw [hR, hBc]
    omega
  have hstab : Nat.card (MulAction.stabilizer (ConjAct H) u) ≤ 2 * q := by
    let f : MulAction.stabilizer (ConjAct H) u → centralizer ({u} : Set H) := fun g =>
      ⟨g.val.ofConjAct, by
        apply mem_centralizer_singleton_iff.mpr
        have hg := g.property
        change g.val.ofConjAct * u * g.val.ofConjAct⁻¹ = u at hg
        exact mul_inv_eq_iff_eq_mul.mp hg⟩
    exact (Nat.card_le_card_of_injective f (by
      intro x y hh
      apply Subtype.ext
      have he : ConjAct.ofConjAct x.val = ConjAct.ofConjAct y.val :=
        congrArg (fun a : centralizer ({u} : Set H) => (a : H)) hh
      exact ConjAct.ofConjAct.injective he)).trans hc
  have horbit : O.ncard * Nat.card (MulAction.stabilizer (ConjAct H) u) = 2 * q ^ 3 := by
    have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct H) u)
    rw [Nat.card_prod] at hh
    have hg : Nat.card (ConjAct H) = Nat.card H :=
      Nat.card_congr ConjAct.toConjAct.toEquiv.symm
    rw [hg, hH] at hh
    exact hh
  have hlow : q ^ 2 ≤ O.ncard := by
    have hp : 0 < 2 * q := by omega
    have hh : q ^ 2 * (2 * q) ≤ O.ncard * (2 * q) := by
      calc
        q ^ 2 * (2 * q) = 2 * q ^ 3 := by ring
        _ = O.ncard * Nat.card (MulAction.stabilizer (ConjAct H) u) := horbit.symm
        _ ≤ _ := Nat.mul_le_mul_left _ hstab
    nlinarith
  have hcover : O = (R : Set H) \ (B : Set H) :=
    Set.eq_of_subset_of_ncard_le hO (hdiff ▸ hlow)
  intro x hx
  by_contra hxB
  have hxO : x ^ 2 ∈ O := hcover ▸ ⟨hx, hxB⟩
  obtain ⟨g, hg⟩ := hxO
  let y := (MulAut.conj g.ofConjAct⁻¹) x
  have hy : y ^ 2 = u := by
    change ((MulAut.conj g.ofConjAct⁻¹) x) ^ 2 = u
    rw [← map_pow, ← hg]
    change (MulAut.conj g.ofConjAct⁻¹) ((MulAut.conj g.ofConjAct) u) = u
    simp only [MulAut.conj_apply]
    group
  have hyc : y ∈ centralizer ({u} : Set H) := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hy]
    exact (Commute.self_pow y 2).eq
  have hu1 : u = 1 := hy.symm.trans (hsq y hyc)
  exact huB (hu1 ▸ B.one_mem)

end Subgroup
