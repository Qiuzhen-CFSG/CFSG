module

public import Theory.GroupTheory.PGroup.OrderSixteenNormalFourCore
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Involution fusion in an order-sixteen core

The order-sixteen core from `OrderSixteenNormalFourCore` has cyclic center of
order four.  Its normal elementary four-groups inject into the three
nonidentity elements of the quotient by the center.  Every noncentral
involution lies in one of these normal fours.  Conjugation acts on this set;
the absence of an ambient normal four means that no point is fixed, so the
action is transitive.  This gives ambient fusion of every core involution into
the chosen normal four.

The argument is the elementary four-group orbit calculation in
Janko--Thompson, Math. Z. 113 (1970), §4, printed pp.392--393.
-/

open Subgroup
open scoped Pointwise

namespace MulAction

private theorem transitive_of_card_le_three {K X : Type*} [Group K] [MulAction K X] [Finite X]
    (hcard : Nat.card X ≤ 3) (hmove : ∀ x : X, ∃ g : K, g • x ≠ x) (x y : X) :
    ∃ g : K, g • x = y := by
  by_contra hn
  have hsize (z : X) : 1 < (orbit K z).ncard := by
    obtain ⟨g, hg⟩ := hmove z
    exact (Set.one_lt_ncard_iff).mpr
      ⟨g • z, z, mem_orbit z g, mem_orbit_self z, hg⟩
  have hdisj : Disjoint (orbit K x) (orbit K y) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨g, rfl⟩ ⟨h, hh⟩
    apply hn
    refine ⟨h⁻¹ * g, ?_⟩
    change h • y = g • x at hh
    rw [mul_smul, ← hh, inv_smul_smul]
  have hb := Set.ncard_le_card (orbit K x ∪ orbit K y)
  rw [Set.ncard_union_eq hdisj] at hb
  have hx := hsize x
  have hy := hsize y
  omega

end MulAction

namespace Subgroup

private theorem four_noncentral {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    ∃ x : P, x ∈ E ∧ x ∉ center P := by
  by_contra! h
  have hc : IsCyclic E := isCyclic_of_injective (inclusion h) (inclusion_injective h)
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) hE hc

private theorem four_count {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hcard : Nat.card P = 16) (hZ : Nat.card (center P) = 4)
    (hrank : ∀ U : Subgroup P, IsElementaryAbelian 2 U → Nat.card U < 8) :
    Nat.card {E : Subgroup P // E.Normal ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4} ≤ 3 := by
  classical
  let X := {E : Subgroup P // E.Normal ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4}
  have hex (E : X) : ∃ x : P, x ∈ E.val ∧ x ∉ center P := by
    let : IsElementaryAbelian 2 E.val := E.property.2.1
    exact four_noncentral E.val E.property.2.2
  choose x hx hxZ using hex
  let f : X → {q : P ⧸ center P // q ≠ 1} := fun E =>
    ⟨QuotientGroup.mk' (center P) (x E), fun h => hxZ E ((QuotientGroup.eq_one_iff _).mp h)⟩
  have hf : Function.Injective f := by
    intro E F h
    apply Subtype.ext
    by_contra hne
    let : E.val.Normal := E.property.1
    let : F.val.Normal := F.property.1
    let : IsElementaryAbelian 2 E.val := E.property.2.1
    let : IsElementaryAbelian 2 F.val := F.property.2.1
    have hd : x F / x E ∈ center P := QuotientGroup.eq_iff_div_mem.mp
      (congrArg Subtype.val h).symm
    have hxc : x F ∈ centralizer (E.val : Set P) := by
      have hh := (centralizer (E.val : Set P)).mul_mem
        (center_le_centralizer _ hd) (le_centralizer E.val (hx E))
      simpa only [div_mul_cancel] using hh
    have hxE := mem_four_of_square_eq_one_of_elementary_card_lt_eight hrank E.val
      E.property.2.2 (elemPow_eq_one_of_isElementaryAbelian (A := F.val) (x F) (hx F)) hxc
    have hi := inf_card_two_of_distinct_normal_fours hrank E.val F.val
      E.property.2.2 F.property.2.2 hne
    exact hxZ F (central_of_normal_card_two (E.val ⊓ F.val) hi ⟨hxE, hx F⟩)
  have hQ : Nat.card (P ⧸ center P) = 4 := by
    have hh := (center P).card_eq_card_quotient_mul_card_subgroup
    rw [hcard, hZ] at hh
    omega
  have hc : Nat.card {q : P ⧸ center P // q ≠ 1} = 3 := by
    change Nat.card ↥(({1} : Set (P ⧸ center P))ᶜ) = 3
    rw [Nat.card_coe_set_eq, Set.ncard_compl, hQ, Set.ncard_singleton]
  exact (Nat.card_le_card_of_injective f hf).trans (by omega)

private theorem involution_four {P : Type*} [Group P] [Finite P]
    (hcard : Nat.card P = 16) (hZ : Nat.card (center P) = 4)
    (hrank : ∀ U : Subgroup P, IsElementaryAbelian 2 U → Nat.card U < 8)
    (t : P) (ht : t ^ 2 = 1) (htZ : t ∉ center P) :
    ∃ F : Subgroup P, F.Normal ∧ IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧ t ∈ F := by
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center P) 2 (by rw [hZ]; decide)
  have hz2 : (z : P) ^ 2 = 1 :=
    congrArg Subtype.val (by simpa [hz] using pow_orderOf_eq_one z)
  have hZz : zpowers (z : P) ≤ center P := zpowers_le.mpr z.property
  have htz : t ∉ zpowers (z : P) := fun h => htZ (hZz h)
  let F := zpowers (z : P) ⊔ zpowers t
  let : IsElementaryAbelian 2 (zpowers (z : P)) := IsElementaryAbelian.zpowers_of_pow_eq_one hz2
  let : IsElementaryAbelian 2 (zpowers t) := IsElementaryAbelian.zpowers_of_pow_eq_one ht
  have hcomm : zpowers t ≤ centralizer (zpowers (z : P) : Set P) :=
    le_centralizer_iff.mp (hZz.trans (center_le_centralizer _))
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.sup_of_le_centralizer hcomm
  have hF : Nat.card F = 4 := by
    rw [card_sup_zpowers_of_normalizing_involution _ t ht htz
      ((hcomm.trans (centralizer_le_normalizer _)) (mem_zpowers t)), Nat.card_zpowers,
      Subgroup.orderOf_coe, hz]
  let C := center P ⊔ zpowers t
  have hC : Nat.card C = 8 := by
    rw [card_sup_zpowers_of_normalizing_involution _ t ht htZ
      (by rw [(center P).normalizer_eq_top]; trivial), hZ]
  have hCi : C.index = 2 := by
    have hh := C.card_mul_index
    rw [hcard, hC] at hh
    omega
  let : C.Normal := normal_of_index_eq_two hCi
  have hFC : F ≤ C := sup_le (hZz.trans le_sup_left) le_sup_right
  have hCF : C ≤ centralizer (F : Set P) := by
    apply sup_le (center_le_centralizer _) (le_centralizer_iff.mp ?_)
    exact sup_le (hZz.trans (center_le_centralizer _)) (le_centralizer _)
  exact ⟨F, normal_four_of_normal_centralizing_overgroup hrank F C hF hFC hCF,
    inferInstance, hF, mem_sup_right (mem_zpowers t)⟩

private theorem fusion_of_three_fours
    {K : Type*} [Group K] [Finite K] (P : Subgroup K) [P.Normal]
    (hcount : Nat.card {E : Subgroup P // E.Normal ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4} ≤ 3)
    (hno : ∀ U : Subgroup K, U.Normal → IsElementaryAbelian 2 U → Nat.card U ≠ 4)
    (E F : Subgroup P) [E.Normal] [F.Normal]
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hF : Nat.card F = 4) :
    ∃ g : K, F.map (MulAut.conjNormal g).toMonoidHom = E := by
  let X := {U : Subgroup P // U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4}
  have hstable (g : K) (U : X) :
      (U.val.map (MulAut.conjNormal g).toMonoidHom).Normal ∧
      IsElementaryAbelian 2 (U.val.map (MulAut.conjNormal g).toMonoidHom) ∧
      Nat.card (U.val.map (MulAut.conjNormal g).toMonoidHom) = 4 := by
    let : U.val.Normal := U.property.1
    let : IsElementaryAbelian 2 U.val := U.property.2.1
    exact ⟨(MulAut.conjNormal g).normal_map_iff.mpr inferInstance,
      IsElementaryAbelian.map _,
      (card_map_of_injective (MulAut.conjNormal g).injective).trans U.property.2.2⟩
  let : MulAction K X := {
    smul := fun g U => ⟨U.val.map (MulAut.conjNormal g).toMonoidHom, hstable g U⟩
    one_smul := fun U => Subtype.ext (by
      change U.val.map (MulAut.conjNormal 1 : MulAut P).toMonoidHom = U.val
      rw [show (MulAut.conjNormal 1 : MulAut P).toMonoidHom = MonoidHom.id P by
        ext x
        simp, Subgroup.map_id])
    mul_smul := fun g h U => Subtype.ext (by
      change U.val.map (MulAut.conjNormal (g * h) : MulAut P).toMonoidHom =
        (U.val.map (MulAut.conjNormal h).toMonoidHom).map (MulAut.conjNormal g).toMonoidHom
      rw [map_map]
      congr 1
      ext x
      simp) }
  have hmove (U : X) : ∃ g : K, g • U ≠ U := by
    by_contra! hn
    have hfixed (g : K) : U.val.map (MulAut.conjNormal g).toMonoidHom = U.val :=
      congrArg Subtype.val (hn g)
    let : IsElementaryAbelian 2 U.val := U.property.2.1
    have hnormal : (U.val.map P.subtype).Normal := by
      refine ⟨fun x hx g => ?_⟩
      obtain ⟨x, hx, rfl⟩ := hx
      have hm : MulAut.conjNormal g x ∈ U.val :=
        hfixed g ▸ mem_map_of_mem (MulAut.conjNormal g).toMonoidHom hx
      exact ⟨MulAut.conjNormal g x, hm, rfl⟩
    exact hno (U.val.map P.subtype) hnormal (IsElementaryAbelian.map _)
      ((card_map_of_injective P.subtype_injective).trans U.property.2.2)
  obtain ⟨g, hg⟩ := MulAction.transitive_of_card_le_three hcount hmove
    (⟨F, inferInstance, inferInstance, hF⟩ : X) (⟨E, inferInstance, inferInstance, hE⟩ : X)
  exact ⟨g, congrArg Subtype.val hg⟩

/-- Every involution of the order-sixteen core is fused into its normal four. -/
public theorem exists_isConj_mem_normal_four_of_order_sixteen
    {K : Type*} [Group K] [Finite K] (P : Subgroup K) [P.Normal]
    (hP : IsPGroup 2 P) (hcard : Nat.card P = 16)
    (hrank : ∀ U : Subgroup K, IsElementaryAbelian 2 U → Nat.card U < 8)
    (hno : ∀ U : Subgroup K, U.Normal → IsElementaryAbelian 2 U → Nat.card U ≠ 4)
    (E : Subgroup P) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (t : P) (ht : orderOf t = 2) :
    ∃ u : E, IsConj (t : K) ((u : P) : K) := by
  obtain ⟨hcyc, hZ, _⟩ :=
    dihedral_central_factor_of_order_sixteen_of_no_ambient_normal_four P hP hcard hrank hno E hE
  let : IsCyclic (center P) := hcyc
  have hr := elementary_card_lt_eight_of_subgroup hrank P
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  by_cases htZ : t ∈ center P
  · have htE : t ∈ E := mem_four_of_square_eq_one_of_elementary_card_lt_eight hr E hE ht2
      (center_le_centralizer _ htZ)
    exact ⟨⟨t, htE⟩, IsConj.refl _⟩
  obtain ⟨F, hFn, hFe, hF, htF⟩ := involution_four hcard hZ hr t ht2 htZ
  let : F.Normal := hFn
  let : IsElementaryAbelian 2 F := hFe
  obtain ⟨g, hg⟩ := fusion_of_three_fours P (four_count hcard hZ hr) hno E F hE hF
  have hu : MulAut.conjNormal g t ∈ E := hg ▸ mem_map_of_mem _ htF
  refine ⟨⟨MulAut.conjNormal g t, hu⟩, ?_⟩
  exact isConj_iff.mpr ⟨g, rfl⟩

end Subgroup
