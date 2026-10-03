module

public import Theory.GroupTheory.AbelianSylowAutomizer
public import Theory.GroupTheory.PGroup.RankTwoHomocyclicFrattini
public import Theory.GroupTheory.CardFourAutomorphismStabilizer

/-!
# Local centralizers of rank-two homocyclic Sylow two-subgroups

For an abelian Sylow two-subgroup with Klein-four Frattini quotient, its
nontrivial normalizer action has order three. An automorphism of order three
acts freely away from the identity: this holds on the Frattini quotient by
the order-four stabilizer bound, and the displacement homomorphism lifts
surjectivity from that quotient by the nongenerating property of Frattini.
Consequently the normalizer inside the centralizer of any nonidentity Sylow
element centralizes the whole Sylow subgroup. Burnside transfer gives a normal
two-complement in that element centralizer, with the original Sylow subgroup
retained by subtype.

Source: Richard Brauer, *Some applications of the theory of blocks of
characters of finite groups. II*, J. Algebra 1 (1964), §VI, p.317;
source copy: `refs/original/brauer-homocyclic-sylow/brauer-blocks-II-1964.pdf`.
No simplicity or trivial odd-core hypothesis is used.
-/

open Subgroup
open scoped IsMulCommutative

private theorem fixed_point_eq_one_of_card_four
    {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q = 4)
    (b : MulAut Q) (hb : orderOf b = 3) (x : Q) (hx : b x = x) : x = 1 := by
  by_contra hne
  let K := MulAction.stabilizer (MulAut Q) x
  have hbound : Nat.card K ≤ 2 :=
    card_mulAut_subgroup_le_two_of_fixed_point hQ x hne K (fun f hf => hf)
  have hdiv : 3 ∣ Nat.card K := by
    rw [← hb]
    exact K.orderOf_dvd_natCard hx
  have hpos : 0 < Nat.card K := Nat.card_pos
  have := Nat.le_of_dvd hpos hdiv
  omega

/-- An order-three automorphism of an abelian two-group with Klein-four
Frattini quotient fixes only the identity. -/
public theorem MulAut.fixed_point_eq_one_of_order_three_of_kleinFour_frattini
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    [IsKleinFour (A ⧸ frattini A)] (hA : IsPGroup 2 A)
    (a : MulAut A) (ha : orderOf a = 3) (x : A) (hx : a x = x) : x = 1 := by
  let q := quotientAut (frattini A)
  let b := q a
  have hbne : b ≠ 1 := by
    intro h
    have hmem : a ∈ q.ker := h
    have hne : (⟨a, hmem⟩ : q.ker) ≠ 1 := by
      intro hh
      have hone : a = 1 := congrArg Subtype.val hh
      simp [hone] at ha
    have hd := (isPGroup_quotientAut_frattini_kernel hA).dvd_orderOf hne
    have hd2 : 2 ∣ orderOf a := by simpa only [← Subgroup.orderOf_coe] using hd
    rw [ha] at hd2
    norm_num at hd2
  have hb : orderOf b = 3 := by
    apply orderOf_eq_prime _ hbne
    change q a ^ 3 = 1
    rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  let _ : IsMulCommutative (A ⧸ frattini A) := IsKleinFour.isMulCommutative
  let d : A →* A := a.toMonoidHom / MonoidHom.id A
  let dQ : (A ⧸ frattini A) →* (A ⧸ frattini A) :=
    b.toMonoidHom / MonoidHom.id _
  have hiQ : Function.Injective dQ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro y hy
    change y = 1
    apply fixed_point_eq_one_of_card_four IsKleinFour.card_four b hb y
    have he : b y / y = 1 := hy
    exact div_eq_one.mp he
  have hsQ := Finite.surjective_of_injective hiQ
  let π := QuotientGroup.mk' (frattini A)
  have hd (y : A) : π (d y) = dQ (π y) := by
    change π (a y / y) = b (π y) / π y
    rw [map_div]
    exact congrArg (fun z => z / π y) (quotientAut_apply_mk (frattini A) a y).symm
  have hgen : d.range ⊔ frattini A = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨z, hz⟩ := hsQ (π y)
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (frattini A) z
    have he : π y = π (d w) := hz.symm.trans (hd w).symm
    have hphi : y / d w ∈ frattini A := QuotientGroup.eq_iff_div_mem.mp he
    have h1 : y / d w ∈ d.range ⊔ frattini A :=
      (show frattini A ≤ d.range ⊔ frattini A from le_sup_right) hphi
    have h2 : d w ∈ d.range ⊔ frattini A :=
      (show d.range ≤ d.range ⊔ frattini A from le_sup_left) ⟨w, rfl⟩
    simpa using (d.range ⊔ frattini A).mul_mem h1 h2
  have hs : Function.Surjective d := MonoidHom.range_eq_top.mp (frattini_nongenerating hgen)
  have hi : Function.Injective d := (Finite.injective_iff_surjective).mpr hs
  apply hi
  change a x / x = d 1
  rw [hx, div_self', map_one]

namespace Sylow

private theorem normalizer_action_ne_bot_of_not_le
    {G : Type*} [Group G] (S : Sylow 2 G)
    (h : ¬ normalizer (S : Set G) ≤ centralizer (S : Set G)) :
    (S : Subgroup G).normalizerMonoidHom.range ≠ ⊥ := by
  intro hb
  have hf := MonoidHom.range_eq_bot_iff.mp hb
  apply h
  intro g hg
  have hk : (⟨g, hg⟩ : normalizer (S : Set G)) ∈
      (S : Subgroup G).normalizerMonoidHom.ker := by
    change (S : Subgroup G).normalizerMonoidHom ⟨g, hg⟩ = 1
    rw [hf]
    rfl
  rwa [normalizerMonoidHom_ker] at hk

/-- The actual normalizer action on a rank-two homocyclic Sylow subgroup has
order three whenever the normalizer does not centralize the subgroup. -/
public theorem card_normalizer_action_eq_three_of_equiv_prod_zmod
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (h : ¬ normalizer (S : Set G) ≤ centralizer (S : Set G)) :
    Nat.card (S : Subgroup G).normalizerMonoidHom.range = 3 := by
  let : IsMulCommutative S := ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
  let := isKleinFour_frattini_quotient_of_equiv_prod_zmod (by omega : 1 ≤ n) e
  exact S.card_normalizer_action_eq_three (normalizer_action_ne_bot_of_not_le S h)

/-- A noncentralizing normalizer supplies an actual automorphism of order three. -/
public theorem exists_order_three_normalizer_automorphism_of_equiv_prod_zmod
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (h : ¬ normalizer (S : Set G) ≤ centralizer (S : Set G)) :
    ∃ a : MulAut S, a ∈ (S : Subgroup G).normalizerMonoidHom.range ∧ orderOf a = 3 := by
  have hc := S.card_normalizer_action_eq_three_of_equiv_prod_zmod hn e h
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3
    (show 3 ∣ Nat.card (S : Subgroup G).normalizerMonoidHom.range by rw [hc])
  exact ⟨a, a.property, by simpa only [Subgroup.orderOf_coe] using ha⟩

/-- Every nonidentity automorphism in the actual normalizer image acts freely
on the nonidentity elements of an abelian Sylow subgroup of Frattini rank two. -/
public theorem normalizer_automorphism_fixed_point_eq_one
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    [IsMulCommutative S] [IsKleinFour (S ⧸ frattini S)]
    (a : MulAut S) (ha : a ∈ (S : Subgroup G).normalizerMonoidHom.range)
    (hne : a ≠ 1) (s : S) (hfix : a s = s) : s = 1 := by
  have hrange : (S : Subgroup G).normalizerMonoidHom.range ≠ ⊥ := by
    intro h
    exact hne (by simpa only [h, mem_bot] using ha)
  have hc := S.card_normalizer_action_eq_three hrange
  have horder : orderOf a = 3 := by
    have hd := (S : Subgroup G).normalizerMonoidHom.range.orderOf_dvd_natCard ha
    rw [hc] at hd
    exact (Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left
      (fun h => hne (orderOf_eq_one_iff.mp h))
  exact a.fixed_point_eq_one_of_order_three_of_kleinFour_frattini S.isPGroup' horder s hfix

/-- Coordinate form of the fixed-point-free normalizer action. -/
public theorem normalizer_automorphism_fixed_point_eq_one_of_equiv_prod_zmod
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (a : MulAut S) (ha : a ∈ (S : Subgroup G).normalizerMonoidHom.range)
    (hne : a ≠ 1) (s : S) (hfix : a s = s) : s = 1 := by
  let : IsMulCommutative S := ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
  let := isKleinFour_frattini_quotient_of_equiv_prod_zmod (by omega : 1 ≤ n) e
  exact S.normalizer_automorphism_fixed_point_eq_one a ha hne s hfix

/-- An abelian Sylow subgroup lies in the centralizer of each of its elements. -/
public theorem le_centralizer_singleton
    {G : Type*} [Group G] (S : Sylow 2 G) [IsMulCommutative S] (s : S) :
    (S : Subgroup G) ≤ centralizer ({(s : G)} : Set G) := by
  intro x hx
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mul_comm (⟨x, hx⟩ : S) s))

/-- Inside a nonidentity element centralizer, the normalizer of the actual
Sylow subgroup centralizes that subgroup. -/
public theorem normalizer_centralizer_sylow_le_centralizer
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    [IsMulCommutative S] [IsKleinFour (S ⧸ frattini S)]
    (s : S) (hs : s ≠ 1) :
    let P := S.subtype (le_centralizer_singleton S s)
    normalizer (P : Set (centralizer ({(s : G)} : Set G))) ≤ centralizer (P : Set _) := by
  let C := centralizer ({(s : G)} : Set G)
  let P := S.subtype (le_centralizer_singleton S s)
  change normalizer (P : Set C) ≤ centralizer (P : Set C)
  intro g hg
  have hgN : (g : G) ∈ normalizer (S : Set G) := by
    apply mem_normalizer_fintype
    intro x hx
    let xC : C := ⟨x, le_centralizer_singleton S s hx⟩
    have hxP : xC ∈ P := hx
    have hz := (mem_normalizer_iff.mp hg xC).mp hxP
    exact hz
  let a := (S : Subgroup G).normalizerMonoidHom ⟨g, hgN⟩
  have hfix : a s = s := by
    apply Subtype.ext
    change (g : G) * (s : G) * (g : G)⁻¹ = (s : G)
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp g.property)
  have ha : a = 1 := by
    by_contra hne
    exact hs (S.normalizer_automorphism_fixed_point_eq_one a ⟨⟨g, hgN⟩, rfl⟩ hne s hfix)
  intro x hx
  apply Subtype.ext
  have hax := congrArg (fun f : MulAut S => f (⟨x, hx⟩ : S)) ha
  have heq := congrArg Subtype.val hax
  change (g : G) * (x : G) * (g : G)⁻¹ = (x : G) at heq
  exact (mul_inv_eq_iff_eq_mul.mp heq).symm

/-- Burnside transfer in an element centralizer gives a normal odd-order
complement to the original Sylow subgroup, retained by subtype. -/
public theorem exists_normal_two_complement_centralizer
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    [IsMulCommutative S] [IsKleinFour (S ⧸ frattini S)]
    (s : S) (hs : s ≠ 1) :
    let C := centralizer ({(s : G)} : Set G)
    ∃ (N : Subgroup C) (_hN : N.Normal),
      Odd (Nat.card N) ∧ IsPGroup 2 (C ⧸ N) ∧
      N.IsComplement' (S.subtype (le_centralizer_singleton S s) : Subgroup C) := by
  let C := centralizer ({(s : G)} : Set G)
  let P := S.subtype (le_centralizer_singleton S s)
  have hP : normalizer (P : Set C) ≤ centralizer (P : Set C) :=
    normalizer_centralizer_sylow_le_centralizer S s hs
  let f := MonoidHom.transferSylow P hP
  refine ⟨f.ker, inferInstance, ?_, ?_, MonoidHom.ker_transferSylow_isComplement' P hP⟩
  · exact Nat.not_even_iff_odd.mp (fun h =>
      MonoidHom.not_dvd_card_ker_transferSylow P hP h.two_dvd)
  · exact (P.isPGroup'.to_subgroup f.range).of_equiv
      (QuotientGroup.quotientKerEquivRange f).symm

/-- The actual Sylow subgroup and normal two-complement inside a nonidentity
Sylow-element centralizer, from the homocyclic coordinates. Noncentrality of
the ambient normalizer is not needed for this conclusion. -/
public theorem exists_normal_two_complement_centralizer_of_equiv_prod_zmod
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (s : S) (hs : s ≠ 1) :
    let C := centralizer ({(s : G)} : Set G)
    ∃ (hSC : (S : Subgroup G) ≤ C) (N : Subgroup C) (_hN : N.Normal),
      Odd (Nat.card N) ∧ IsPGroup 2 (C ⧸ N) ∧
      N.IsComplement' (S.subtype hSC : Subgroup C) := by
  let : IsMulCommutative S := ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
  let := isKleinFour_frattini_quotient_of_equiv_prod_zmod (by omega : 1 ≤ n) e
  exact ⟨S.le_centralizer_singleton s, S.exists_normal_two_complement_centralizer s hs⟩

/-- Normal odd-order kernel and two-group quotient in the actual element
centralizer; a convenient projection of the complement statement. -/
public theorem exists_odd_normal_subgroup_centralizer_of_equiv_prod_zmod
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (s : S) (hs : s ≠ 1) :
    let C := centralizer ({(s : G)} : Set G)
    ∃ (N : Subgroup C) (_hN : N.Normal), Odd (Nat.card N) ∧ IsPGroup 2 (C ⧸ N) := by
  obtain ⟨_, N, hN, hodd, hquot, _⟩ :=
    S.exists_normal_two_complement_centralizer_of_equiv_prod_zmod hn e s hs
  exact ⟨N, hN, hodd, hquot⟩

/-- Fusion of homocyclic Sylow elements is realized by the actual normalizer. -/
public theorem conj_eq_normalizer_conj_of_equiv_prod_zmod
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) {n : ℕ}
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (x g : G) (hx : x ∈ S) (hy : g⁻¹ * x * g ∈ S) :
    ∃ u ∈ normalizer (S : Set G), g⁻¹ * x * g = u⁻¹ * x * u := by
  let : IsMulCommutative S := ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
  exact S.conj_eq_normalizer_conj_of_mem x g hx hy

end Sylow
