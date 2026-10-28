module

public import Theory.GroupTheory.PGroup.NormalEightCriticalSubgroup
public import Theory.GroupTheory.PGroup.AbelianRankTwoHomocyclic
public import Theory.GroupTheory.PGroup.CriticalSubgroupAutomorphisms
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.GroupTheory.HomocyclicSylowCentralizers

/-!
# Odd automorphisms with an abelian critical subgroup

An abelian critical subgroup with first omega of order four has a Klein four
Frattini quotient. Restriction to the critical subgroup, followed by action
on its Frattini quotient, has a two-group kernel. If the full automorphism
group is not a two-group, its image in the group of order six has order
divisible by three. Cauchy's theorem supplies an order-three automorphism.
Its restriction has the same order, so the two cyclic factors of the
critical subgroup have equal order.

Sources: Thompson's critical subgroup theorem, Gorenstein, *Finite Groups*,
Theorem 5.3.11; the abelian reduction for MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3. No assertion about involutions outside
the critical subgroup is made here.
-/

open Subgroup

namespace IsCriticalPSubgroup

/-- A rank-two abelian critical subgroup detects an automorphism of order three. -/
public theorem exists_order_three_of_not_isPGroup_mulAut {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hAut : ¬ IsPGroup 2 (MulAut P)) {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hfour : Nat.card (omega₁ C (p := 2)) = 4) :
    ∃ a : MulAut P, orderOf a = 3 := by
  let : C.Characteristic := hC.characteristic
  let : IsKleinFour (C ⧸ frattini C) :=
    (hP.to_subgroup C).isKleinFour_frattini_quotient_of_card_omega_one_eq_four hfour
  let r := MulAut.characteristic C
  let q := quotientAut (frattini C)
  let f := q.comp r
  have hr : IsPGroup 2 r.ker :=
    C.isPGroup_characteristic_restriction_kernel_of_centralizer_le
      (hP.to_subgroup C) (by rw [hC.centralizer_eq]; exact map_subtype_le _)
  have hk : IsPGroup 2 f.ker :=
    (isPGroup_quotientAut_frattini_kernel (hP.to_subgroup C)).comap_of_ker_isPGroup r hr
  have hn : ¬ IsPGroup 2 f.range := by
    intro hh
    have ht := hh.comap_of_ker_isPGroup f hk
    rw [MonoidHom.comap_range_self] at ht
    exact hAut (ht.of_equiv Subgroup.topEquiv)
  have hd : Nat.card f.range ∣ 6 := by
    rw [← IsKleinFour.card_mulAut (C ⧸ frattini C)]
    exact card_subgroup_dvd_card _
  have hle : Nat.card f.range ≤ 6 := Nat.le_of_dvd (by decide) hd
  have h3 : 3 ∣ Nat.card f.range := by
    by_contra hh
    have heq : Nat.card f.range = 1 ∨ Nat.card f.range = 2 := by
      interval_cases Nat.card f.range <;> omega
    rcases heq with h | h
    · exact hn (IsPGroup.of_card (n := 0) h)
    · exact hn (IsPGroup.of_card (n := 1) h)
  exact exists_prime_orderOf_dvd_card' 3 (h3.trans (Subgroup.card_range_dvd f))

/-- Under a non-two-group automorphism action, the abelian critical subgroup
is a product of two cyclic groups of the same nontrivial two-power order. -/
public theorem homocyclic_of_not_isPGroup_mulAut
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hAut : ¬ IsPGroup 2 (MulAut P)) {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hfour : Nat.card (omega₁ C (p := 2)) = 4) :
    ∃ n : ℕ, 1 ≤ n ∧ Nonempty
      (C ≃* (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^n)))) := by
  obtain ⟨a, ha⟩ := exists_order_three_of_not_isPGroup_mulAut hP hAut hC hfour
  let : C.Characteristic := hC.characteristic
  have hr : orderOf (MulAut.characteristic C a) = 3 :=
    (hC.orderOf_restrict_eq_of_coprime hP a (by rw [ha]; decide)).trans ha
  exact (hP.to_subgroup C).exists_equiv_prod_self_zmod_of_orderOf_aut_eq_three
    hfour (MulAut.characteristic C a) hr

/-- A critical subgroup of order four forces the whole group to be abelian
in the central-four, no-normal-eight situation. -/
public theorem isMulCommutative_of_card_eq_four {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (hcard : Nat.card C = 4) : IsMulCommutative P := by
  have ho : omega₁ C (p := 2) = ⊤ :=
    eq_top_of_card_eq _ ((hC.card_omega_one_eq_four hno hZ).trans hcard.symm)
  have hCc : C ≤ center P := by
    intro c hc
    have hm : c ∈ (omega₁ C (p := 2)).map C.subtype := ⟨⟨c, hc⟩, ho ▸ mem_top _, rfl⟩
    rw [hC.omega_one_map_eq_center hno hZ] at hm
    exact map_subtype_le _ hm
  have htop : C = ⊤ := by
    apply top_unique
    intro x _
    have hx : x ∈ centralizer (C : Set P) := by
      intro c hc
      exact (mem_center_iff.mp (hCc hc) x).symm
    rw [hC.centralizer_eq] at hx
    exact map_subtype_le _ hx
  exact center_eq_top_iff.mp (top_unique (htop ▸ hCc))

/-- The homocyclic exponent is at least four when the whole group is nonabelian. -/
public theorem homocyclic_large_of_not_isPGroup_mulAut
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hAut : ¬ IsPGroup 2 (MulAut P)) (hnonab : ¬ IsMulCommutative P)
    {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty
      (C ≃* (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^n)))) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hC.homocyclic_of_not_isPGroup_mulAut hP hAut
    (hC.card_omega_one_eq_four hno hZ)
  refine ⟨n, ?_, ⟨e⟩⟩
  by_contra hsmall
  have he : n = 1 := by omega
  have hc : Nat.card C = 4 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, he]
    norm_num
  exact hnonab (hC.isMulCommutative_of_card_eq_four hno hZ hc)

/-- The detected order-three automorphism fixes no nonidentity element of
an abelian critical subgroup with first omega of order four. -/
public theorem exists_order_three_free_on_critical
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hAut : ¬ IsPGroup 2 (MulAut P)) {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hfour : Nat.card (omega₁ C (p := 2)) = 4) :
    ∃ a : MulAut P, orderOf a = 3 ∧ ∀ c ∈ C, a c = c → c = 1 := by
  obtain ⟨a, ha⟩ := hC.exists_order_three_of_not_isPGroup_mulAut hP hAut hfour
  let : C.Characteristic := hC.characteristic
  let : IsKleinFour (C ⧸ frattini C) :=
    (hP.to_subgroup C).isKleinFour_frattini_quotient_of_card_omega_one_eq_four hfour
  have hr : orderOf (MulAut.characteristic C a) = 3 :=
    (hC.orderOf_restrict_eq_of_coprime hP a (by rw [ha]; decide)).trans ha
  refine ⟨a, ha, ?_⟩
  intro c hc hfix
  have he : (⟨c, hc⟩ : C) = 1 :=
    (MulAut.characteristic C a).fixed_point_eq_one_of_order_three_of_kleinFour_frattini
      (hP.to_subgroup C) hr ⟨c, hc⟩ (Subtype.ext hfix)
  exact congrArg Subtype.val he

end IsCriticalPSubgroup
