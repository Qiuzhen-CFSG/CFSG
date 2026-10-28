module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.LinearThree.Transport

/-!
# The three-part of an invariant subgroup of two exchanged factors

Let `P` and `Q` be self-normalizing Sylow two-subgroups of finite groups
`A` and `B`. If `P × Q` normalizes `W ≤ A × B` and an automorphism exchanges
the axes and preserves `W`, the exponent of three in `|W|` is even.
Consequently W cannot have Sylow three-subgroups of order three.

Write `K₁ = {a | (a,1) ∈ W}`, `K₂ = {b | (1,b) ∈ W}`, and
`N = K₁ × K₂`. Independent coordinate conjugation gives `[W,P × Q] ≤ N`.
The group `H = ⟨W,P × Q⟩` normalizes N, and the image of `P × Q` in H/N
is normal. Sylow self-normalization and the Frattini argument force H/N
to be a two-group. Thus N, W and H have the same three-part. The exchanging
automorphism identifies the two axis intersections, so `|N| = |K₁|²`.

This is the intrinsic product calculation used for the L₃(2) exclusion
in Aschbacher–Smith, combined manuscript (1 March 2004), proof of 15.3.27,
printed p.1130 (PDF p.1147). The geometric coordinates and their application
to the actual Y₊ remain with the source assembly. No solvability or
order-two hypothesis on the exchanging automorphism is required.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearThree.ProductCalculation
variable {A B : Type*} [Group A] [Group B]

private abbrev axisFirst (W : Subgroup (A × B)) : Subgroup A :=
  W.comap (MonoidHom.inl A B)

private abbrev axisSecond (W : Subgroup (A × B)) : Subgroup B :=
  W.comap (MonoidHom.inr A B)

private theorem mem_axisFirst {W : Subgroup (A × B)} {a : A} :
    a ∈ axisFirst W ↔ (a, 1) ∈ W := Iff.rfl

private theorem mem_axisSecond {W : Subgroup (A × B)} {b : B} :
    b ∈ axisSecond W ↔ (1, b) ∈ W := Iff.rfl

private theorem axis_product_le (W : Subgroup (A × B)) :
    (axisFirst W).prod (axisSecond W) ≤ W := by
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  simpa using W.mul_mem (mem_axisFirst.mp ha) (mem_axisSecond.mp hb)

private theorem prod_card (U : Subgroup A) (V : Subgroup B) :
    Nat.card (U.prod V) = Nat.card U * Nat.card V := by
  rw [Nat.card_congr (U.prodEquiv V).toEquiv, Nat.card_prod]

variable [Finite A] [Finite B]

private def prodSylow (P : Sylow 2 A) (Q : Sylow 2 B) : Sylow 2 (A × B) :=
  Sylow.ofCard ((P : Subgroup A).prod Q) (by
    rw [prod_card, P.card_eq_multiplicity, Q.card_eq_multiplicity, Nat.card_prod,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, pow_add])

private theorem prodSylow_self_normalizing (P : Sylow 2 A) (Q : Sylow 2 B)
    (hP : normalizer (P : Set A) = (P : Subgroup A))
    (hQ : normalizer (Q : Set B) = (Q : Subgroup B)) :
    normalizer (prodSylow P Q : Set (A × B)) = (prodSylow P Q : Subgroup (A × B)) := by
  apply le_antisymm ?_ (prodSylow P Q).le_normalizer
  intro x hx
  change x.1 ∈ P ∧ x.2 ∈ Q
  constructor
  · change x.1 ∈ (P : Subgroup A)
    rw [← hP]
    apply mem_normalizer_iff.mpr
    intro a
    simpa [prodSylow, Prod.mul_def, mem_prod] using
      mem_normalizer_iff.mp hx (a, 1)
  · change x.2 ∈ (Q : Subgroup B)
    rw [← hQ]
    apply mem_normalizer_iff.mpr
    intro b
    simpa [prodSylow, Prod.mul_def, mem_prod] using
      mem_normalizer_iff.mp hx (1, b)

omit [Finite A] [Finite B] in
/-- Coordinate axes are stable under conjugation by every product element. -/
private theorem normalizes_axis_product (W H : Subgroup (A × B))
    (hH : H ≤ normalizer (W : Set (A × B))) :
    H ≤ normalizer ((axisFirst W).prod (axisSecond W) : Set (A × B)) := by
  apply le_normalizer_iff.mpr
  intro h hh n hn
  constructor
  · apply mem_axisFirst.mpr
    have he := le_normalizer_iff.mp hH h hh (n.1, 1) (mem_axisFirst.mp hn.1)
    simpa [Prod.mul_def] using he
  · apply mem_axisSecond.mpr
    have he := le_normalizer_iff.mp hH h hh (1, n.2) (mem_axisSecond.mp hn.2)
    simpa [Prod.mul_def] using he

omit [Finite A] [Finite B] in
/-- Each coordinate commutator lies in its corresponding axis intersection. -/
private theorem commutator_le_axis_product (W : Subgroup (A × B))
    (P : Subgroup A) (Q : Subgroup B)
    (hW : P.prod Q ≤ normalizer (W : Set (A × B))) :
    ⁅W, P.prod Q⁆ ≤ (axisFirst W).prod (axisSecond W) := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro t ht w hw
  have hc := le_normalizer_iff_commutator_le_right.mp hW
  constructor
  · apply mem_axisFirst.mpr
    have he := hc (commutator_mem_commutator (show (t.1, 1) ∈ P.prod Q from
      ⟨ht.1, Q.one_mem⟩) hw)
    simpa [commutatorElement_def, Prod.mul_def, mul_assoc] using he
  · apply mem_axisSecond.mpr
    have he := hc (commutator_mem_commutator (show (1, t.2) ∈ P.prod Q from
      ⟨P.one_mem, ht.2⟩) hw)
    simpa [commutatorElement_def, Prod.mul_def, mul_assoc] using he

/-- Kill the mixed commutators, then use Sylow self-normalization in the quotient. -/
private theorem three_part_eq_of_commutator
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    (hT : normalizer (T : Set G) = (T : Subgroup G))
    (W N : Subgroup G) (hNW : N ≤ W)
    (hN : W ⊔ (T : Subgroup G) ≤ normalizer (N : Set G))
    (hc : ⁅W, (T : Subgroup G)⁆ ≤ N) :
    (Nat.card W).factorization 3 = (Nat.card N).factorization 3 := by
  let H := W ⊔ (T : Subgroup G)
  have hNH : N ≤ H := hNW.trans le_sup_left
  let K := N.subgroupOf H
  let _ : K.Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr hN
  let f := QuotientGroup.mk' K
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hS : normalizer (S : Set H) = (S : Subgroup H) :=
    self_normalizing_sylow_subtype T hT H le_sup_right
  have hgen : W.subgroupOf H ⊔ (S : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show W ≤ H from le_sup_left)]
    change W ⊔ ((T : Subgroup G).subgroupOf H).map H.subtype = _
    rw [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)]
    rw [← MonoidHom.range_eq_map, H.range_subtype]
  have hcomm : ⁅(W.subgroupOf H).map f, (S : Subgroup H).map f⁆ ≤ ⊥ := by
    rw [← map_commutator, map_le_iff_le_comap]
    change ⁅W.subgroupOf H, (S : Subgroup H)⁆ ≤ f.ker
    rw [QuotientGroup.ker_mk']
    apply commutator_le.mpr
    intro w hw t ht
    exact hc (commutator_mem_commutator hw ht)
  have hnormal : ((S : Subgroup H).map f).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    have hg : (W.subgroupOf H).map f ⊔ (S : Subgroup H).map f = ⊤ := by
      rw [← Subgroup.map_sup, hgen, map_top_of_surjective f (QuotientGroup.mk'_surjective K)]
    rw [← hg]
    exact sup_le (le_normalizer_iff_commutator_le_right.mpr (hcomm.trans bot_le))
      (Subgroup.le_normalizer)
  have htwo : IsPGroup 2 (H ⧸ K) :=
    image_isTwoGroup_of_normal_sylow S hS f (QuotientGroup.mk'_surjective K) hnormal
  have hz : (Nat.card (H ⧸ K)).factorization 3 = 0 := by
    obtain ⟨n, hn⟩ := htwo.exists_card_eq
    rw [hn]
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have heq : (Nat.card H).factorization 3 = (Nat.card N).factorization 3 := by
    have hk : Nat.card K = Nat.card N :=
      Nat.card_congr (subgroupOfEquivOfLe hNH).toEquiv
    rw [K.card_eq_card_quotient_mul_card_subgroup,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hz,
      zero_add, hk]
  apply le_antisymm
  · rw [← heq]
    exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (card_dvd_of_le (show W ≤ H from le_sup_left)) 3
  · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (card_dvd_of_le hNW) 3

omit [Finite A] [Finite B] in
private theorem axis_cards_eq (W : Subgroup (A × B)) (τ : MulAut (A × B))
    (hτ : ((⊤ : Subgroup A).prod (⊥ : Subgroup B)).map τ.toMonoidHom =
      (⊥ : Subgroup A).prod (⊤ : Subgroup B))
    (hW : W.map τ.toMonoidHom = W) :
    Nat.card (axisFirst W) = Nat.card (axisSecond W) := by
  have hf : (axisFirst W).map (MonoidHom.inl A B) =
      W ⊓ (⊤ : Subgroup A).prod (⊥ : Subgroup B) := by
    ext ⟨a, b⟩
    constructor
    · rintro ⟨x, hx, he⟩
      cases he
      exact ⟨hx, by simp [mem_prod]⟩
    · rintro ⟨hw, hab⟩
      have hb : b = 1 := hab.2
      subst b
      exact ⟨a, hw, rfl⟩
  have hs : (axisSecond W).map (MonoidHom.inr A B) =
      W ⊓ (⊥ : Subgroup A).prod (⊤ : Subgroup B) := by
    ext ⟨a, b⟩
    constructor
    · rintro ⟨x, hx, he⟩
      cases he
      exact ⟨hx, by simp [mem_prod]⟩
    · rintro ⟨hw, hab⟩
      have ha : a = 1 := hab.1
      subst a
      exact ⟨b, hw, rfl⟩
  have hi : (W ⊓ (⊤ : Subgroup A).prod (⊥ : Subgroup B)).map τ.toMonoidHom =
      W ⊓ (⊥ : Subgroup A).prod (⊤ : Subgroup B) := by
    rw [Subgroup.map_inf _ _ _ τ.injective, hW, hτ]
  calc
    Nat.card (axisFirst W) = Nat.card ((axisFirst W).map (MonoidHom.inl A B)) :=
      (card_map_of_injective (by intro x y h; exact congrArg Prod.fst h)).symm
    _ = Nat.card ↥(W ⊓ (⊤ : Subgroup A).prod (⊥ : Subgroup B)) := by rw [hf]
    _ = Nat.card ((W ⊓ (⊤ : Subgroup A).prod (⊥ : Subgroup B)).map τ.toMonoidHom) :=
      (card_map_of_injective τ.injective).symm
    _ = Nat.card ((axisSecond W).map (MonoidHom.inr A B)) := by rw [hi, hs]
    _ = Nat.card (axisSecond W) :=
      card_map_of_injective (by intro x y h; exact congrArg Prod.snd h)

/-- Independent Sylow normalization and exchange make the three-part a square.
The forward axis equality alone suffices for this stronger numerical statement. -/
theorem three_part_exponent_even (P : Sylow 2 A) (Q : Sylow 2 B)
    (hP : normalizer (P : Set A) = (P : Subgroup A))
    (hQ : normalizer (Q : Set B) = (Q : Subgroup B))
    (W : Subgroup (A × B))
    (hn : (P : Subgroup A).prod Q ≤ normalizer (W : Set (A × B)))
    (τ : MulAut (A × B))
    (hτ : ((⊤ : Subgroup A).prod (⊥ : Subgroup B)).map τ.toMonoidHom =
      (⊥ : Subgroup A).prod (⊤ : Subgroup B))
    (hW : W.map τ.toMonoidHom = W) : Even ((Nat.card W).factorization 3) := by
  let N := (axisFirst W).prod (axisSecond W)
  have he : (Nat.card W).factorization 3 = (Nat.card N).factorization 3 := by
    apply three_part_eq_of_commutator (prodSylow P Q)
      (prodSylow_self_normalizing P Q hP hQ) W N (axis_product_le W)
    · apply normalizes_axis_product
      exact sup_le W.le_normalizer hn
    · exact commutator_le_axis_product W P Q hn
  rw [he, prod_card, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Finsupp.add_apply, axis_cards_eq W τ hτ hW]
  exact ⟨_, rfl⟩

/-- The intrinsic product obstruction for the linear-three orbit.
The two axis equalities match the geometric coordinate contract; no condition
on the order of the exchanging automorphism is imposed. -/
theorem not_sylow_three_card_eq_three (P : Sylow 2 A) (Q : Sylow 2 B)
    (hP : normalizer (P : Set A) = (P : Subgroup A))
    (hQ : normalizer (Q : Set B) = (Q : Subgroup B))
    (W : Subgroup (A × B))
    (hn : (P : Subgroup A).prod Q ≤ normalizer (W : Set (A × B)))
    (τ : MulAut (A × B))
    (hτ : ((⊤ : Subgroup A).prod (⊥ : Subgroup B)).map τ.toMonoidHom =
      (⊥ : Subgroup A).prod (⊤ : Subgroup B))
    (_hτ' : ((⊥ : Subgroup A).prod (⊤ : Subgroup B)).map τ.toMonoidHom =
      (⊤ : Subgroup A).prod (⊥ : Subgroup B))
    (hW : W.map τ.toMonoidHom = W) :
    ¬ (∀ R : Sylow 3 W, Nat.card R = 3) := by
  intro hthree
  let R : Sylow 3 W := Sylow.nonempty.some
  have hv : (Nat.card W).factorization 3 = 1 := by
    apply Nat.pow_right_injective (by decide : 1 < 3)
    simpa only [pow_one] using R.card_eq_multiplicity.symm.trans (hthree R)
  have he := three_part_exponent_even P Q hP hQ W hn τ hτ hW
  rw [hv] at he
  exact (by decide : ¬ Even (1 : ℕ)) he

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearThree.ProductCalculation
