module

public import Theory.GroupTheory.SylowCentralizerTrivialIntersection
public import Theory.GroupTheory.SylowCentralizerInversion

/-!
# Involutions in external Sylow cosets

Let `P` be a nonnormal Sylow two-subgroup containing the centralizer of each
of its nonidentity elements, and put `L = N(P)`. Every `P`-coset outside `L`
contains an involution. If `P` has two distinct involutions, then `[L:P] > 1`.

Write `m = [G:L]`, `n = [L:P]`, and let `t` count the involutions of `P`.
Trivial intersection and Sylow conjugacy give exactly `m * t` involutions
in `G`. Every involution of `L` lies in `P`. External-coset uniqueness
therefore gives `(m - 1) * t ≤ (m - 1) * n`. Since `m > 1`, we get `t ≤ n`.
Conjugating any involution of `P` by representatives of `L/P` gives distinct
involutions, so `n ≤ t`. Equality makes the external-coset injection surjective.

This is the initial involution count in Suzuki, *Finite groups with nilpotent
centralizers* (1961), Part I, Theorem 2, printed pp. 429–430. The argument here
uses the Sylow trivial-intersection property to perform the count directly.
-/

open Subgroup
open scoped Pointwise
namespace Sylow
variable {G : Type*} [Group G] [Finite G]

private lemma eq_of_common_nonidentity (P : Sylow 2 G)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      centralizer ({x} : Set G) ≤ (P : Subgroup G))
    (Q R : Sylow 2 G) {x : G} (hx : x ≠ 1)
    (hxQ : x ∈ (Q : Subgroup G)) (hxR : x ∈ (R : Subgroup G)) : Q = R := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  have hmem (S : Sylow 2 G) (hS : x ∈ (S : Subgroup G)) :
      (MulAut.conj g) x ∈ (g • S : Sylow 2 G) :=
    Set.smul_mem_smul_set hS
  have hyP : (MulAut.conj g) x ∈ (P : Subgroup G) := hg ▸ hmem Q hxQ
  have hyR := hmem R hxR
  have hyne : (MulAut.conj g) x ≠ 1 := by simpa using hx
  have he : g • R = P := P.eq_of_inf_ne_bot_of_centralizer_le (g • R) hcent (by
    intro h
    have hy : (MulAut.conj g) x ∈ (P : Subgroup G) ⊓ (g • R : Sylow 2 G) := ⟨hyP, hyR⟩
    rw [h] at hy
    exact hyne hy)
  exact smul_left_cancel g (hg.trans he.symm)

private lemma involution_count (P : Sylow 2 G)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      centralizer ({x} : Set G) ≤ (P : Subgroup G)) :
    Nat.card {x : G // orderOf x = 2} =
      (normalizer (P : Set G)).index * Nat.card {x : P // orderOf x = 2} := by
  classical
  let D := Σ Q : Sylow 2 G, {x : Q // orderOf x = 2}
  let f (z : D) : {x : G // orderOf x = 2} :=
    ⟨z.2.val, by rw [Subgroup.orderOf_coe]; exact z.2.property⟩
  have hi : Function.Injective f := by
    rintro ⟨Q, x, hx⟩ ⟨R, y, hy⟩ he
    have hxy : (x : G) = y := congrArg Subtype.val he
    have hne : (x : G) ≠ 1 := by
      intro h
      have ho : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
      simp [h] at ho
    have hQR := eq_of_common_nonidentity P hcent Q R hne x.property (hxy ▸ y.property)
    subst R
    have he : x = y := Subtype.ext hxy
    subst y
    rfl
  have hs : Function.Surjective f := by
    rintro ⟨x, hx⟩
    have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (by
      simpa only [Nat.card_zpowers, pow_one] using hx : Nat.card (zpowers x) = 2 ^ 1)
    obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
    refine ⟨⟨Q, ⟨⟨x, hQ (mem_zpowers x)⟩, ?_⟩⟩, rfl⟩
    rwa [← Subgroup.orderOf_coe]
  rw [← Nat.card_eq_of_bijective f ⟨hi, hs⟩]
  let := Fintype.ofFinite (Sylow 2 G)
  have he (Q : Sylow 2 G) : Nat.card {x : Q // orderOf x = 2} =
      Nat.card {x : P // orderOf x = 2} := by
    apply Nat.card_congr
    exact (Q.equiv P).toEquiv.subtypeEquiv (fun x => by
      change orderOf x = 2 ↔ orderOf ((Q.equiv P).toMonoidHom x) = 2
      rw [orderOf_injective (Q.equiv P).toMonoidHom (Q.equiv P).injective])
  rw [show Nat.card D = ∑ Q : Sylow 2 G, Nat.card {x : Q // orderOf x = 2} from Nat.card_sigma]
  simp_rw [he]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    P.card_eq_index_normalizer]

omit [Finite G] in
private lemma mem_of_involution_mem_normalizer (P : Sylow 2 G)
    {x : G} (hx : orderOf x = 2) (hn : x ∈ normalizer (P : Set G)) :
    x ∈ (P : Subgroup G) := by
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (by
    simpa only [Nat.card_zpowers, pow_one] using hx : Nat.card (zpowers x) = 2 ^ 1)
  have hm : x ∈ zpowers x ⊓ normalizer (P : Set G) := ⟨mem_zpowers x, hn⟩
  rw [hp.inf_normalizer_sylow P] at hm
  exact hm.2

private lemma relIndex_le_involution_count (P : Sylow 2 G)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      centralizer ({x} : Set G) ≤ (P : Subgroup G))
    (t : P) (ht : orderOf t = 2) :
    (P : Subgroup G).relIndex (normalizer (P : Set G)) ≤
      Nat.card {x : P // orderOf x = 2} := by
  classical
  let L := normalizer (P : Set G)
  let C := L ⧸ (P : Subgroup G).subgroupOf L
  let a (q : C) : L := q.out
  have htne : (t : G) ≠ 1 := by
    intro h
    have : t = 1 := Subtype.ext h
    simp [this] at ht
  let f (q : C) : {x : P // orderOf x = 2} :=
    ⟨⟨(MulAut.conj (a q : G)) t,
      (mem_normalizer_iff.mp (a q).property (t : G)).mp t.property⟩, by
        rw [← Subgroup.orderOf_coe]
        exact (orderOf_injective (MulAut.conj (a q : G)).toMonoidHom
          (MulAut.conj (a q : G)).injective t).trans (by rwa [Subgroup.orderOf_coe])⟩
  have hi : Function.Injective f := by
    intro q r h
    have he := congrArg (fun z : {x : P // orderOf x = 2} => ((z.val : P) : G)) h
    change (a q : G) * (t : G) * (a q : G)⁻¹ =
      (a r : G) * (t : G) * (a r : G)⁻¹ at he
    have hc : (a q : G)⁻¹ * (a r : G) ∈ centralizer ({(t : G)} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg (fun z : G => (a q : G)⁻¹ * z * (a r : G)) he.symm
      simpa [mul_assoc] using hh
    have heq : (a q : C) = (a r : C) := QuotientGroup.eq.mpr (hcent t t.property htne hc)
    simpa only [a, Quotient.out_eq'] using heq
  exact Nat.card_le_card_of_injective f hi

private lemma card_compl {α : Type*} [Finite α] (p : α → Prop) :
    Nat.card {x : α // ¬ p x} = Nat.card α - Nat.card {x : α // p x} := by
  classical
  let := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

private lemma card_ne {α : Type*} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
  rw [card_compl]
  congr 1
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨⟨a, rfl⟩⟩⟩

private lemma external_involution_count (P : Sylow 2 G)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      centralizer ({x} : Set G) ≤ (P : Subgroup G)) :
    Nat.card {x : G // orderOf x = 2 ∧ x ∉ (P : Subgroup G)} =
      ((normalizer (P : Set G)).index - 1) * Nat.card {x : P // orderOf x = 2} := by
  let I := {x : G // orderOf x = 2}
  let e : {x : G // orderOf x = 2 ∧ x ∉ (P : Subgroup G)} ≃
      {x : I // ¬ (x : G) ∈ (P : Subgroup G)} := {
    toFun := fun x => ⟨⟨x, x.property.1⟩, x.property.2⟩
    invFun := fun x => ⟨x.val, x.val.property, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let e' : {x : I // (x : G) ∈ (P : Subgroup G)} ≃ {x : P // orderOf x = 2} := {
    toFun := fun x => ⟨⟨x.val, x.property⟩, by
      rw [← Subgroup.orderOf_coe]; exact x.val.property⟩
    invFun := fun x => ⟨⟨x.val, by rw [Subgroup.orderOf_coe]; exact x.property⟩, x.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, card_compl, Nat.card_congr e']
  change Nat.card {x : G // orderOf x = 2} - _ = _
  rw [involution_count P hcent, Nat.sub_mul, one_mul]

/-- Centralizer containment saturates the Sylow cosets outside the normalizer with
involutions. Two distinct involutions make the relative normalizer index exceed one. -/
public theorem involution_coset_saturation_of_centralizer_le (P : Sylow 2 G)
    (hn : ¬ (P : Subgroup G).Normal)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      centralizer ({x} : Set G) ≤ (P : Subgroup G))
    (htwo : ∃ t u : P, orderOf t = 2 ∧ orderOf u = 2 ∧ t ≠ u) :
    (∀ g : G, g ∉ normalizer (P : Set G) →
      ∃ t : G, orderOf t = 2 ∧ g⁻¹ * t ∈ (P : Subgroup G)) ∧
      1 < (P : Subgroup G).relIndex (normalizer (P : Set G)) := by
  classical
  let L := normalizer (P : Set G)
  let C := L ⧸ (P : Subgroup G).subgroupOf L
  let X := {q : G ⧸ L // q ≠ ((1 : G) : G ⧸ L)}
  let D := {x : G // orderOf x = 2 ∧ x ∉ (P : Subgroup G)}
  let e : G ⧸ (P : Subgroup G) ≃ (G ⧸ L) × C :=
    quotientEquivProdOfLE (show (P : Subgroup G) ≤ L from le_normalizer)
  have hef (g : G) : (e (g : G ⧸ (P : Subgroup G))).1 = (g : G ⧸ L) := rfl
  have hnL (x : D) : (x : G) ∉ L :=
    fun hx => x.property.2 (mem_of_involution_mem_normalizer P x.property.1 hx)
  let f (x : D) : X × C :=
    (⟨(e ((x : G) : G ⧸ (P : Subgroup G))).1, by
      rw [hef]
      intro h
      exact hnL x (by simpa using L.inv_mem (QuotientGroup.eq.mp h))⟩,
     (e ((x : G) : G ⧸ (P : Subgroup G))).2)
  -- Inverters lie in `P`, so two external involutions cannot share a `P`-coset.
  have hi : Function.Injective f := by
    intro x y h
    have he : e ((x : G) : G ⧸ (P : Subgroup G)) =
        e ((y : G) : G ⧸ (P : Subgroup G)) :=
      Prod.ext (congrArg (fun z : X × C => z.1.val) h) (congrArg (fun z : X × C => z.2) h)
    have hm := QuotientGroup.eq.mp (e.injective he)
    have hxi : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_left (by
      simpa [pow_two, x.property.1] using pow_orderOf_eq_one (x : G))
    have hyi : (y : G)⁻¹ = y := inv_eq_of_mul_eq_one_left (by
      simpa [pow_two, y.property.1] using pow_orderOf_eq_one (y : G))
    apply Subtype.ext
    exact P.eq_of_involutions_mul_inv_mem_of_centralizer_le hcent x.property.2
      (by simpa only [x.property.1] using pow_orderOf_eq_one (x : G))
      (by simpa only [y.property.1] using pow_orderOf_eq_one (y : G))
      (by simpa only [hxi, hyi] using hm)
  have hc : Nat.card (X × C) = (L.index - 1) * (P : Subgroup G).relIndex L := by
    rw [Nat.card_prod, card_ne]
    rfl
  have hd : Nat.card D = (L.index - 1) * Nat.card {x : P // orderOf x = 2} :=
    external_involution_count P hcent
  have hm : 1 < L.index := L.one_lt_index_of_ne_top (fun h => hn (normalizer_eq_top_iff.mp h))
  -- Cancel the positive number of external normalizer cosets.
  have hle : Nat.card {x : P // orderOf x = 2} ≤ (P : Subgroup G).relIndex L := by
    have hh := Nat.card_le_card_of_injective f hi
    rw [hd, hc] at hh
    exact Nat.le_of_mul_le_mul_left hh (by omega)
  obtain ⟨t, u, ht, hu, htu⟩ := htwo
  have heq : Nat.card {x : P // orderOf x = 2} = (P : Subgroup G).relIndex L :=
    hle.antisymm (relIndex_le_involution_count P hcent t ht)
  have hs : Function.Surjective f :=
    (hi.bijective_of_nat_card_le (by rw [hc, hd, heq])).2
  constructor
  · intro g hg
    have hq : (e (g : G ⧸ (P : Subgroup G))).1 ≠ ((1 : G) : G ⧸ L) := by
      rw [hef]
      intro h
      exact hg (by simpa using L.inv_mem (QuotientGroup.eq.mp h))
    obtain ⟨x, hx⟩ := hs (⟨(e (g : G ⧸ (P : Subgroup G))).1, hq⟩,
      (e (g : G ⧸ (P : Subgroup G))).2)
    refine ⟨x, x.property.1, ?_⟩
    apply QuotientGroup.eq.mp
    apply e.injective
    exact (Prod.ext (congrArg (fun z : X × C => z.1.val) hx)
      (congrArg (fun z : X × C => z.2) hx)).symm
  · rw [← heq]
    let : Nontrivial {x : P // orderOf x = 2} :=
      ⟨⟨⟨t, ht⟩, ⟨u, hu⟩, fun h => htu (congrArg Subtype.val h)⟩⟩
    let := Fintype.ofFinite {x : P // orderOf x = 2}
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card

end Sylow
