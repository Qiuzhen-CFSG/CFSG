module

public import Theory.GroupTheory.PGroup.NormalEightAbelianCriticalAction
public import Theory.GroupTheory.SylowPGroupAutomizer

/-!
# Cubic actions realized by a Sylow normalizer

For an abelian critical subgroup with first omega of order four, every
automorphism subgroup which is not a two-group contains an element of order
three. Restriction to the critical subgroup and then its Frattini quotient
has a two-group kernel and image of order dividing six. Cauchy's theorem
therefore applies inside the given automorphism subgroup.

Applied to the image of a Sylow normalizer, this produces a cubic action
realized by ambient conjugation. Its restriction to the critical subgroup
is fixed-point-free. The conjugating element itself is not asserted to have
order three.

Source: MacWilliams, Trans. AMS 150 (1970), Case 1.2, pp.376–377,
DOI 10.1090/S0002-9947-1970-0276324-3. This strengthens the abstract
automorphism reduction with the realization needed for ambient fusion.
-/

open Subgroup

namespace IsCriticalPSubgroup

/-- A non-two-group of automorphisms contains a cubic action detected by
an abelian critical subgroup of rank two. -/
public theorem exists_order_three_mem_automorphism_subgroup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hfour : Nat.card (omega₁ C (p := 2)) = 4)
    (A : Subgroup (MulAut P)) (hA : ¬ IsPGroup 2 A) :
    ∃ a : MulAut P, a ∈ A ∧ orderOf a = 3 := by
  let : C.Characteristic := hC.characteristic
  let : IsKleinFour (C ⧸ frattini C) :=
    (hP.to_subgroup C).isKleinFour_frattini_quotient_of_card_omega_one_eq_four hfour
  let r := MulAut.characteristic C
  let q := quotientAut (frattini C)
  let f := (q.comp r).comp A.subtype
  have hr : IsPGroup 2 r.ker :=
    C.isPGroup_characteristic_restriction_kernel_of_centralizer_le
      (hP.to_subgroup C) (by rw [hC.centralizer_eq]; exact map_subtype_le _)
  have hkfull : IsPGroup 2 (q.comp r).ker :=
    (isPGroup_quotientAut_frattini_kernel (hP.to_subgroup C)).comap_of_ker_isPGroup r hr
  have hk : IsPGroup 2 f.ker := hkfull.comap_subtype
  have hn : ¬ IsPGroup 2 f.range := by
    intro hh
    have ht := hh.comap_of_ker_isPGroup f hk
    rw [MonoidHom.comap_range_self] at ht
    exact hA (ht.of_equiv Subgroup.topEquiv)
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
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 3
    (h3.trans (Subgroup.card_range_dvd f))
  exact ⟨a, a.property, (orderOf_coe a).trans ha⟩

end IsCriticalPSubgroup

namespace Sylow

/-- Nontrivial outer normalizer action yields a realized cubic automorphism
acting freely on an abelian critical subgroup of rank two. -/
public theorem exists_normalizer_order_three_free_on_abelian_critical
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    {C : Subgroup S} (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hfour : Nat.card (omega₁ C (p := 2)) = 4) :
    ∃ g : normalizer (S : Set G),
      orderOf ((S : Subgroup G).normalizerMonoidHom g) = 3 ∧
      ∀ c ∈ C, (S : Subgroup G).normalizerMonoidHom g c = c → c = 1 := by
  let f := (S : Subgroup G).normalizerMonoidHom
  have hA : ¬ IsPGroup 2 f.range := fun h =>
    hnorm (S.normalizer_eq_sup_centralizer_of_isPGroup_action h)
  obtain ⟨a, ⟨g, rfl⟩, ha⟩ :=
    hC.exists_order_three_mem_automorphism_subgroup S.isPGroup' hfour f.range hA
  let : C.Characteristic := hC.characteristic
  let : IsKleinFour (C ⧸ frattini C) :=
    (S.isPGroup'.to_subgroup C).isKleinFour_frattini_quotient_of_card_omega_one_eq_four
      hfour
  have hr : orderOf (MulAut.characteristic C (f g)) = 3 :=
    (hC.orderOf_restrict_eq_of_coprime S.isPGroup' (f g) (by rw [ha]; decide)).trans ha
  refine ⟨g, ha, ?_⟩
  intro c hc hfix
  have he : (⟨c, hc⟩ : C) = 1 :=
    (MulAut.characteristic C (f g)).fixed_point_eq_one_of_order_three_of_kleinFour_frattini
      (S.isPGroup'.to_subgroup C) hr ⟨c, hc⟩ (Subtype.ext hfix)
  exact congrArg Subtype.val he

end Sylow
