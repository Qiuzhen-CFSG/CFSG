module
public import Theory.GroupAction.IrreducibleNormalIntersection
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.RankTwoDisjointAction

/-!
# Containment of elementary planes inducing inner automorphisms

An irreducible elementary plane acting nontrivially by inner automorphisms
on a normal subgroup lies in that subgroup when the ambient prime rank is
at most two. Otherwise irreducibility makes the intersection trivial, and
rank-two orbit counting makes the normal subgroup's order prime to p,
forcing the inner action to be trivial. A coprime quotient lemma lifts
this containment through a normal subgroup of coprime prime-power order.

Source: Aschbacher–Smith, proof of 1.3.4, printed p.510, elementary case.
-/

public section
namespace Subgroup
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem IsNormalizerFrattiniIrreducible.le_normal_of_elementary_inner
    {P : Subgroup G} [IsElementaryAbelian p P]
    (hirr : IsNormalizerFrattiniIrreducible P) (hc : Nat.card P = p ^ 2)
    (hr : primeRank p G ≤ 2) (N : Subgroup G) [N.Normal]
    (hinner : P ≤ N ⊔ centralizer (N : Set G)) (hnc : ⁅N,P⁆ ≠ ⊥) : P ≤ N := by
  let : Fact (IsPGroup p P) := ⟨IsElementaryAbelian.isPGroup p P⟩
  rcases hirr.inf_normal_le_frattini_or_le N with hf | hle
  · have hd : Disjoint P N := by
      apply disjoint_iff.mpr
      apply bot_unique
      simpa only [frattini_eq_bot_of_isElementaryAbelian (p := p) (R := P), map_bot] using hf
    have hcop := coprime_card_of_normalized_disjoint_plane hr P N hc
      le_normalizer_of_normal hd
    have hPC : P ≤ centralizer (N : Set G) := by
      rw [← MulAut.conjNormal_ker_eq_centralizer]
      intro x hx
      have hin : (MulAut.conjNormal x : MulAut N) ∈ MulAut.innerSubgroup N := by
        change x ∈ (MulAut.innerSubgroup N).comap (MulAut.conjNormal : G →* MulAut N)
        rw [MulAut.conjNormal_comap_innerSubgroup]
        exact hinner hx
      let a : MulAut.innerSubgroup N := ⟨MulAut.conjNormal x, hin⟩
      have hp : a ^ p = 1 := by
        apply Subtype.ext
        change (MulAut.conjNormal x : MulAut N) ^ p = 1
        rw [← map_pow]
        have hxpow : x ^ p = 1 := congrArg Subtype.val
          (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p p P) ⟨x,hx⟩)
        rw [hxpow, map_one]
      have hdN : orderOf a ∣ Nat.card N :=
        (_root_.orderOf_dvd_natCard a).trans (card_range_dvd (MulAut.conj : N →* MulAut N))
      have ha : a = 1 := orderOf_eq_one_iff.mp
        (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hp) hdN)
      exact congrArg Subtype.val ha
    exact (hnc (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp hPC))).elim
  · exact hle

omit [Finite G] [Fact p.Prime] in
theorem le_normal_of_le_sup_coprime_pGroup
    {q : ℕ} (P N Q : Subgroup G) [N.Normal]
    (hP : IsPGroup p P) (hQ : IsPGroup q Q) (hcop : Nat.Coprime p q)
    (hle : P ≤ N ⊔ Q) : P ≤ N := by
  let f := QuotientGroup.mk' N
  have hm := map_mono (f := f) hle
  rw [map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at hm
  have hd := (hP.map f).disjoint_of_coprime (hQ.map f) hcop
  have hz : P.map f = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact hd.le_bot ⟨hx, hm hx⟩
  simpa only [f, QuotientGroup.ker_mk'] using (map_eq_bot_iff P).mp hz

end Subgroup
