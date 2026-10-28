module
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Coset.Card

/-!
# Cubic automorphisms supported on complementary generating subgroups

Let `L` and `R` generate a group `V`. Suppose two automorphisms in a finite
subgroup `A` each fix one factor pointwise and preserve the other. If both
have cube one and nine does not divide the order of `A`, one automorphism
is the identity. The factors need not have trivial intersection, and `A`
need not be the full automorphism group.

The automorphisms commute by checking their composites on both generating
subgroups. Their cyclic subgroups meet trivially: an automorphism in the
intersection fixes both factors and hence all of `V`. If neither automorphism
is trivial, their cyclic groups each have order three. Multiplication is then
an injective homomorphism from the product of these cyclic groups into `A`,
contradicting Lagrange's theorem.

This elementary counting argument supplies the independent factor-action
exclusion in Stellmacher (9.1), Journal of Algebra 190 (1997), p.48.
-/

namespace MulAut

private theorem eq_of_eqOn_generating {V : Type*} [Group V]
    {L R : Subgroup V} (hgen : L ⊔ R = ⊤) {f g : MulAut V}
    (hL : ∀ v ∈ L, f v = g v) (hR : ∀ v ∈ R, f v = g v) : f = g := by
  have hle : L ⊔ R ≤ f.toMonoidHom.eqLocus g.toMonoidHom := sup_le hL hR
  rw [hgen] at hle
  exact MulEquiv.ext fun v => hle (Subgroup.mem_top v)

/-- Independent cubic actions on two generating factors cannot both be
nontrivial in an automorphism subgroup whose order is not divisible by nine. -/
public theorem eq_one_or_eq_one_of_disjoint_cubic_actions
    {V : Type*} [Group V] (A : Subgroup (MulAut V)) [Finite A]
    (L R : Subgroup V) (hgen : L ⊔ R = ⊤) (x y : A)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (h9 : ¬ 9 ∣ Nat.card A)
    (hxL : ∀ v ∈ L, (x : MulAut V) v = v)
    (hyR : ∀ v ∈ R, (y : MulAut V) v = v)
    (hxR : ∀ v ∈ R, (x : MulAut V) v ∈ R)
    (hyL : ∀ v ∈ L, (y : MulAut V) v ∈ L) : x = 1 ∨ y = 1 := by
  classical
  by_contra! hne
  have hcomm : Commute x y := by
    apply Subtype.ext
    apply eq_of_eqOn_generating hgen
    · intro v hv
      change (x : MulAut V) ((y : MulAut V) v) = (y : MulAut V) ((x : MulAut V) v)
      rw [hxL _ (hyL v hv), hxL v hv]
    · intro v hv
      change (x : MulAut V) ((y : MulAut V) v) = (y : MulAut V) ((x : MulAut V) v)
      rw [hyR v hv, hyR _ (hxR v hv)]
  have hXL : Subgroup.zpowers x ≤ fixingSubgroup A (L : Set V) :=
    Subgroup.zpowers_le.mpr ((mem_fixingSubgroup_iff A).mpr hxL)
  have hYR : Subgroup.zpowers y ≤ fixingSubgroup A (R : Set V) :=
    Subgroup.zpowers_le.mpr ((mem_fixingSubgroup_iff A).mpr hyR)
  have hd : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers y) := by
    apply Subgroup.disjoint_def.mpr
    intro z hzX hzY
    apply Subtype.ext
    exact eq_of_eqOn_generating hgen
      ((mem_fixingSubgroup_iff A).mp (hXL hzX))
      ((mem_fixingSubgroup_iff A).mp (hYR hzY))
  have hc : ∀ a : Subgroup.zpowers x, ∀ b : Subgroup.zpowers y,
      Commute (a : A) (b : A) := by
    intro a b
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.property
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.property
    rw [← hi, ← hj]
    exact (hcomm.zpow_left i).zpow_right j
  let f := (Subgroup.zpowers x).subtype.noncommCoprod (Subgroup.zpowers y).subtype hc
  have hf : Function.Injective f := Subgroup.mul_injective_of_disjoint hd
  have hdvd := Subgroup.card_dvd_of_injective f hf
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hne.1
  have hycard : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hy3 hne.2
  apply h9
  simpa only [Nat.card_prod, hxcard, hycard] using hdvd

end MulAut
