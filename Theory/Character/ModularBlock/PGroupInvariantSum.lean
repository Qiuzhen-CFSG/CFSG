module
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.CharP.Basic

/-!
# Weighted sums for finite p-group actions

For a finite p-group acting on a finite set, a scalar-valued invariant sum
in characteristic p equals the sum over fixed points. Both the finite
actor and the characteristic hypothesis are essential to the orbit count.

Partition the sum into orbits. Each orbit contributes its cardinality times
one invariant value. A nonfixed orbit has cardinality a positive power of p,
so its contribution vanishes. The singleton orbits correspond precisely to
fixed points. This supplies the finite-sum calculation for subgroup Brauer
restriction, independently of group algebras or modular block definitions.

Ported from revision c3503435 of public/lean-eval/glauberman_zStar,
Submission/ZStar/SubgroupBrauerMap.lean.
-/

public section
noncomputable section
open scoped BigOperators
namespace ModularBlock.SubgroupBrauerMap
universe u v w
attribute [local instance] Fintype.ofFinite

/-- Weighted orbit cancellation for an arbitrary finite action of a finite
`p`-group.  In characteristic `p`, an invariant sum is supported on the fixed
points of the action. -/
theorem sum_eq_sum_fixedPoints_of_smul_invariant
    {p : ℕ} [Fact p.Prime]
    {R : Type u} [CommRing R] [CharP R p]
    {P : Type v} [Group P] [Finite P]
    (hP : IsPGroup p P)
    {α : Type w} [MulAction P α] [Finite α]
    (F : α → R)
    (hF : ∀ q : P, ∀ x : α, F (q • x) = F x) :
    ∑ x : α, F x = ∑ x : MulAction.fixedPoints P α, F x := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let : Fintype (MulAction.fixedPoints P α) := Fintype.ofFinite _
  let : Fintype (MulAction.orbitRel.Quotient P α) := Fintype.ofFinite _
  let g : α → MulAction.orbitRel.Quotient P α := Quotient.mk''
  have hpartition :
      (∑ y : MulAction.orbitRel.Quotient P α,
        ∑ x : {x : α // g x = y}, F x) = ∑ x : α, F x := by
    exact Fintype.sum_fiberwise g F
  rw [← hpartition]
  have hkey : ∀ x : α,
      Fintype.card {y : α // g y = g x} =
        Fintype.card (MulAction.orbit P x) := by
    intro x
    simp only [g, Quotient.eq'']
    congr
  have hfiber_mk (x : α) :
      (∑ y : {y : α // g y = g x}, F y) =
        if x ∈ MulAction.fixedPoints P α then F x else 0 := by
    have hconst (y : {y : α // g y = g x}) : F y = F x := by
      have hy : MulAction.orbitRel P α y.1 x := Quotient.exact' y.2
      rcases hy with ⟨q, hqx⟩
      rw [← hqx]
      exact hF q x
    have hsum :
        (∑ y : {y : α // g y = g x}, F y) =
          (Fintype.card {y : α // g y = g x} : R) * F x := by
      calc
        (∑ y : {y : α // g y = g x}, F y) =
            ∑ _y : {y : α // g y = g x}, F x := by
          apply Fintype.sum_congr
          exact hconst
        _ = (Fintype.card {y : α // g y = g x} : R) * F x := by
          simp [nsmul_eq_mul]
    by_cases hfixed : x ∈ MulAction.fixedPoints P α
    · have hcard : Fintype.card {y : α // g y = g x} = 1 := by
        rw [hkey x]
        exact MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mp hfixed
      rw [hsum, hcard]
      simp [hfixed]
    · obtain ⟨k, hk⟩ := hP.card_orbit x
      have hk' : Fintype.card (MulAction.orbit P x) = p ^ k := by
        simpa [Nat.card_eq_fintype_card] using hk
      have hk0 : k ≠ 0 := by
        intro hk0
        apply hfixed
        rw [MulAction.mem_fixedPoints_iff_card_orbit_eq_one, hk', hk0,
          pow_zero]
      have hpdivOrbit : p ∣ Fintype.card (MulAction.orbit P x) := by
        rw [hk']
        exact dvd_pow_self p hk0
      have hpdivFiber : p ∣ Fintype.card {y : α // g y = g x} := by
        rw [hkey x]
        exact hpdivOrbit
      have hcast : (Fintype.card {y : α // g y = g x} : R) = 0 :=
        (CharP.cast_eq_zero_iff R p _).mpr hpdivFiber
      rw [hsum, hcast]
      simp [hfixed]
  let orbitSum : MulAction.orbitRel.Quotient P α → R := fun y =>
    ∑ x : {x : α // g x = y}, F x
  have hinj : ∀
      (a₁ : MulAction.fixedPoints P α) (_ha₁ : a₁ ∈ Finset.univ)
        (_hne₁ : F a₁ ≠ 0)
      (a₂ : MulAction.fixedPoints P α) (_ha₂ : a₂ ∈ Finset.univ)
        (_hne₂ : F a₂ ≠ 0),
      g a₁.1 = g a₂.1 → a₁ = a₂ := by
    intro a₁ _ _ a₂ _ _ h
    apply Subtype.ext
    exact (MulAction.mem_fixedPoints'.mp a₂.2) a₁.1 (Quotient.exact' h)
  have hsurj : ∀ y : MulAction.orbitRel.Quotient P α,
      y ∈ Finset.univ → orbitSum y ≠ 0 →
        ∃ a : MulAction.fixedPoints P α,
          ∃ ha : a ∈ Finset.univ,
            ∃ hne : F a ≠ 0, g a.1 = y := by
    intro y
    induction y using Quotient.inductionOn' with
    | _ x =>
        intro _ hy
        change orbitSum (g x) ≠ 0 at hy
        have hsum : orbitSum (g x) =
            if x ∈ MulAction.fixedPoints P α then F x else 0 := by
          simpa [orbitSum] using hfiber_mk x
        by_cases hfixed : x ∈ MulAction.fixedPoints P α
        · refine ⟨⟨x, hfixed⟩, Finset.mem_univ _, ?_, rfl⟩
          rw [hsum, if_pos hfixed] at hy
          exact hy
        · rw [hsum, if_neg hfixed] at hy
          exact (hy rfl).elim
  have hvalue : ∀
      (a : MulAction.fixedPoints P α) (_ha : a ∈ Finset.univ)
        (_hne : F a ≠ 0),
      F a = orbitSum (g a.1) := by
    intro a _ _
    simpa [orbitSum, a.2] using (hfiber_mk a.1).symm
  exact Eq.symm (Finset.sum_bij_ne_zero
    (s := (Finset.univ : Finset (MulAction.fixedPoints P α)))
    (t := (Finset.univ : Finset (MulAction.orbitRel.Quotient P α)))
    (f := fun a : MulAction.fixedPoints P α => F a)
    (g := orbitSum)
    (fun a _ _ => g a.1)
    (fun _ _ _ => Finset.mem_univ _)
    hinj hsurj hvalue)

end ModularBlock.SubgroupBrauerMap

