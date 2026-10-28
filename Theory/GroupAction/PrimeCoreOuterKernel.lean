module
public import Theory.GroupAction.BorelActorInner
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The inner part of an action over a prime-core quotient

If a finite actor group modulo its p-core has order q, and q divides its
actual outer-action image, the outer-action kernel has p-power order.
Its image is exactly the inner intersection of the automorphism image.
Both homomorphisms are retained in the statement.

Source application: the cyclic-five first factor in Aschbacher--Smith
14.6.15, printed p.1035. The source consumer constructs the surviving
outer order-five actor; no assertion about ambient centralization is used.
-/

public section
open Subgroup
namespace MulAut
variable {D C : Type*} [Group D] [Group C] [Finite D]

/-- If the whole odd prime quotient survives in the outer action,
the inner part of its image is a prime-group. -/
theorem inner_intersection_isPGroup_of_outer_range {p q : ℕ} (f : D →* MulAut C)
    (hq : q ≠ 0) (hcard : Nat.card (D ⧸ pCore p D) = q)
    (ho : q ∣ Nat.card (((QuotientGroup.mk' (innerSubgroup C)).comp f).range)) :
    IsPGroup p (f.range ⊓ innerSubgroup C : Subgroup _) := by
  let g := (QuotientGroup.mk' (innerSubgroup C)).comp f
  have hd : Nat.card g.ker * q ∣ Nat.card D := by
    have hh := Nat.mul_dvd_mul_left (Nat.card g.ker) ho
    rw [←index_ker g,g.ker.card_mul_index] at hh
    exact hh
  have hD : Nat.card D = Nat.card (pCore p D) * q := by
    rw [←hcard,←index_eq_card]
    exact (pCore p D).card_mul_index.symm
  rw [hD] at hd
  have hk : Nat.card g.ker ∣ Nat.card (pCore p D) :=
    (mul_dvd_mul_iff_right hq).mp hd
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := p) (G := D)).exists_card_dvd_pow
  have hp : IsPGroup p g.ker := IsPGroup.of_card_dvd_pow (hk.trans hn)
  have he : g.ker.map f = f.range ⊓ innerSubgroup C := by
    ext α
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,rfl⟩,(QuotientGroup.eq_one_iff _).mp hx⟩
    · rintro ⟨⟨x,rfl⟩,hx⟩
      exact ⟨x,(QuotientGroup.eq_one_iff _).mpr hx,rfl⟩
  exact he ▸ hp.map f
end MulAut
