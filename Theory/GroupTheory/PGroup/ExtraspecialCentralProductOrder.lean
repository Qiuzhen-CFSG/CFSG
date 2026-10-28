module

public import Theory.ElementaryAbelian.Extraspecial
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Orders of extraspecial central products with cyclic center

In a finite two-group with cyclic center, a nontrivial normal subgroup
contains the unique central involution. Consequently a nontrivial normal
factor commuting with an extraspecial factor meets it in its center, of
order two. The ordinary product formula then computes the ambient order.

This is the order calculation for Hall's central products used in
Janko–Thompson, Math. Z. 113 (1970), §4, pp.392–393.
-/

namespace Subgroup

/-- A nontrivial commuting normal factor meets an extraspecial factor in
order two when the ambient two-group has cyclic center. -/
public theorem card_inf_eq_two_of_extraspecial_of_cyclic_center
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hP : IsPGroup 2 P) (A D : Subgroup P) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] (hD : D ≠ ⊥)
    (hc : D ≤ centralizer (A : Set P)) : Nat.card (A ⊓ D : Subgroup P) = 2 := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).mpr hD
  let Z := (center A).map A.subtype
  have hZcard : Nat.card Z = 2 :=
    (card_map_of_injective A.subtype_injective).trans (IsExtraspecial.center_order_p 2 A)
  have hZcentral : Z ≤ center P := central_of_normal_card_two Z hZcard
  obtain ⟨U, _, hUD, hUcard, hUcentral⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) D inferInstance
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hUcard])
  have hUZ : Z ≤ U := by
    intro z hz
    by_cases hz1 : z = 1
    · simpa only [hz1] using U.one_mem
    have hz2 : z ^ 2 = 1 := by
      have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨z, hz⟩ : Z)))
      change z ^ Nat.card Z = 1 at h
      rwa [hZcard] at h
    have heq : z = (u : P) := congrArg Subtype.val
      (IsCyclic.eq_of_orderOf_eq_two
        (x := (⟨z, hZcentral hz⟩ : center P))
        (y := (⟨u, hUcentral u.property⟩ : center P))
        (orderOf_eq_prime (Subtype.ext hz2) (fun h => hz1 (congrArg Subtype.val h)))
        (by rw [← Subgroup.orderOf_coe]; exact (Subgroup.orderOf_coe u).trans hu))
    exact heq ▸ u.property
  have hinf : A ⊓ D = Z := by
    apply le_antisymm
    · intro x hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      apply mem_center_iff.mpr
      intro a
      exact Subtype.ext (hc hx.2 a a.property)
    · exact le_inf (map_subtype_le _) (hUZ.trans hUD)
  rw [hinf, hZcard]

/-- The central-product order formula for an extraspecial factor and a
nontrivial normal commuting supplement. -/
public theorem card_mul_two_eq_of_extraspecial_of_cyclic_center
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hP : IsPGroup 2 P) (A D : Subgroup P) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] (hD : D ≠ ⊥)
    (hc : D ≤ centralizer (A : Set P)) (hgen : A ⊔ D = ⊤) :
    Nat.card P * 2 = Nat.card A * Nat.card D := by
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes A D
    (hc.trans (centralizer_le_normalizer _))
  rw [card_inf_eq_two_of_extraspecial_of_cyclic_center hP A D hD hc,
    hgen, Nat.card_congr Subgroup.topEquiv.toEquiv] at h
  omega

/-- A nontrivial cyclic commuting factor in such a central product is the
whole center. In particular the displayed cyclic factor is characteristic. -/
public theorem center_eq_cyclic_factor_of_extraspecial_of_cyclic_center
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hP : IsPGroup 2 P) (A D : Subgroup P) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] [IsCyclic D] (hD : D ≠ ⊥)
    (hc : D ≤ centralizer (A : Set P)) (hgen : A ⊔ D = ⊤) :
    center P = D := by
  have hDc : D ≤ center P := by
    have ht : (⊤ : Subgroup P) ≤ centralizer (D : Set P) := by
      rw [← hgen]
      exact sup_le (le_centralizer_iff.mp hc)
        (le_centralizer_iff_isMulCommutative.mpr inferInstance)
    simpa only [coe_top, centralizer_univ] using le_centralizer_iff.mp ht
  have hinf : A ⊓ D = (center A).map A.subtype := by
    apply eq_of_le_of_card_ge
    · intro x hx
      refine ⟨⟨x, hx.1⟩, mem_center_iff.mpr ?_, rfl⟩
      intro a
      exact Subtype.ext (hc hx.2 a a.property)
    · rw [card_map_of_injective A.subtype_injective,
        IsExtraspecial.center_order_p 2 A,
        card_inf_eq_two_of_extraspecial_of_cyclic_center hP A D hD hc]
  apply le_antisymm _ hDc
  intro x hx
  have hxgen : x ∈ A ⊔ D := hgen.symm ▸ mem_top x
  obtain ⟨a, ha, d, hd, rfl⟩ := mem_sup_of_normal_right.mp hxgen
  have haC : a ∈ (center A).map A.subtype := by
    refine ⟨⟨a, ha⟩, mem_center_iff.mpr ?_, rfl⟩
    intro b
    apply Subtype.ext
    apply mul_right_cancel (b := d)
    calc
      (b : P) * a * d = (b : P) * (a * d) := mul_assoc _ _ _
      _ = (a * d) * b := mem_center_iff.mp hx b
      _ = a * b * d := by rw [mul_assoc, ← hc hd b b.property, ← mul_assoc]
  have haD : a ∈ D := (hinf.symm ▸ haC : a ∈ A ⊓ D).2
  exact D.mul_mem haD hd

end Subgroup
