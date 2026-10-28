module

public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.Tactic.IntervalCases

/-!
# Embedding a p-core quotient in a group with small p-part

Suppose a finite group G maps to a finite group H with p-group kernel,
and p² does not divide |H|. The p-core of the image has order one or p
and is a normal Hall subgroup. Schur–Zassenhaus embeds the image modulo
its p-core as a complement in the image. Lifting p-cores through the
surjection identifies this quotient with G/Oₚ(G).

The complement is essential: a quotient of an arbitrary subgroup of H
does not automatically embed in H. This gives the group-theoretic passage
used in Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.25(2), printed p.25, with H = GL₂(p).
-/

namespace MonoidHom

private theorem coprime_card_index_of_not_sq_dvd {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) (hN : IsPGroup p N) (hG : ¬ p ^ 2 ∣ Nat.card G) :
    Nat.Coprime (Nat.card N) N.index := by
  obtain ⟨n, hn⟩ := hN.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra hnle
    exact hG ((Nat.pow_dvd_pow p (by omega : 2 ≤ n)).trans
      (hn ▸ N.card_subgroup_dvd_card))
  interval_cases n
  · simp [hn]
  · rw [pow_one] at hn
    rw [hn, (Fact.out : p.Prime).coprime_iff_not_dvd]
    intro hd
    apply hG
    have hc := N.card_mul_index
    rw [hn] at hc
    rw [← hc, pow_two]
    exact Nat.mul_dvd_mul_left p hd

private theorem exists_injective_quotient_of_coprime {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hc : Nat.Coprime (Nat.card N) N.index) :
    ∃ f : G ⧸ N →* G, Function.Injective f := by
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hc
  let e : K ≃* G ⧸ N := MulEquiv.ofBijective
    ((QuotientGroup.mk' N).comp K.subtype)
    (Subgroup.isComplement_subgroup_right_iff_bijective.mp hK.symm)
  exact ⟨K.subtype.comp e.symm.toMonoidHom, K.subtype_injective.comp e.symm.injective⟩

/-- A representation with p-group kernel in a group whose order is not
divisible by p² gives an embedding of the quotient by the full p-core. -/
public theorem exists_injective_pCore_quotient_of_not_sq_dvd
    {p : ℕ} [Fact p.Prime] {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hker : IsPGroup p f.ker) (hH : ¬ p ^ 2 ∣ Nat.card H) :
    ∃ g : G ⧸ pCore p G →* H, Function.Injective g := by
  have hR : ¬ p ^ 2 ∣ Nat.card f.range := fun h =>
    hH (h.trans f.range.card_subgroup_dvd_card)
  obtain ⟨g, hg⟩ := exists_injective_quotient_of_coprime (pCore p f.range)
    (coprime_card_index_of_not_sq_dvd _ pCore_isPGroup hR)
  let q := (QuotientGroup.mk' (pCore p f.range)).comp f.rangeRestrict
  have hq : q.ker = pCore p G := by
    dsimp [q]
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    apply f.rangeRestrict.comap_pCore_of_ker_isPGroup f.rangeRestrict_surjective
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  let e : (G ⧸ pCore p G) ≃* (f.range ⧸ pCore p f.range) :=
    (QuotientGroup.quotientMulEquivOfEq hq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q
        ((QuotientGroup.mk'_surjective _).comp f.rangeRestrict_surjective))
  exact ⟨f.range.subtype.comp (g.comp e.toMonoidHom),
    f.range.subtype_injective.comp (hg.comp e.injective)⟩

end MonoidHom
