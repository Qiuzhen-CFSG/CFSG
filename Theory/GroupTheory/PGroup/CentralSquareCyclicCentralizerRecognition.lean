module

public import Theory.GroupTheory.PGroup.NoNormalFourClassification
public import Theory.GroupTheory.NormalFourCentralizer
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral
public import Theory.GroupTheory.SemidihedralStandardModel
public import Mathlib.GroupTheory.Nilpotent

/-!
# Recognition from a cyclic centralizer and a central square

A finite two-group containing an elementary four-group is dihedral or
semidihedral if an element of order four has central square and cyclic
centralizer. Both alternatives give equivalences with the concrete models.

Split according to the existence of a normal elementary four-group. In its
presence the centralizer of the four-group has index two. A generator of the
cyclic element centralizer expresses the given element as an odd power, so
that centralizer is precisely the cyclic subgroup of order four. Conjugation
on the normal four supplies an inverting involution. The resulting dihedral
subgroup of order eight is self-normalizing: its two elements of order four
are inverse to each other. The two-group normalizer condition makes it the
whole group. With no normal four-group, use the existing recognition theorem
and convert its presentations to the specified models.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, DOI 10.1215/ijm/1256050927, citing Gorenstein, *Finite Groups*,
5.4.8. The normal-four argument here proves the needed specialization directly.
-/

open Subgroup

private theorem four_not_le_cyclic {P : Type*} [Group P] [Finite P]
    (U C : Subgroup P) [IsElementaryAbelian 2 U] [IsCyclic C]
    (hU : Nat.card U = 4) : ¬ U ≤ C := by
  intro h
  let : IsCyclic U := isCyclic_of_le h
  have hd : Nat.card U ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 U
  norm_num [hU] at hd

private theorem centralizer_eq_zpowers_of_normal_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (U : Subgroup P) [U.Normal] [IsElementaryAbelian 2 U] (hU : Nat.card U = 4)
    (u : P) [IsCyclic (centralizer ({u} : Set P))] :
    centralizer ({u} : Set P) = zpowers u := by
  classical
  let C := centralizer ({u} : Set P)
  let D := centralizer (U : Set P)
  have huD : u ∉ D := by
    intro h
    exact four_not_le_cyclic U C hU (fun v hv =>
      mem_centralizer_singleton_iff.mpr (h v hv))
  have hi : D.index = 2 := by
    have hb := centralizer_index_le_two_of_normal_four hP U hU
    have hz := D.index_ne_zero_of_finite
    have ho : D.index ≠ 1 := fun h => huD (index_eq_one.mp h ▸ mem_top u)
    change D.index ≤ 2 at hb
    omega
  obtain ⟨a, ha⟩ := C.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have huC : u ∈ C := mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨k, _, hku⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp (ha.symm ▸ huC))
  have hodd : Odd k := by
    apply Nat.not_even_iff_odd.mp
    rintro ⟨j, hj⟩
    apply huD
    rw [← hku, hj, ← two_mul, pow_mul]
    exact D.pow_mem (D.sq_mem_of_index_two hi a) j
  have hau : a ∈ zpowers u := by
    rw [← hku, mem_zpowers_pow_iff]
    obtain ⟨n, hn⟩ := hP.exists_orderOf_eq_pow a
    rw [hn]
    exact (Nat.coprime_two_right.mpr hodd).pow_right n
  apply le_antisymm
  · change C ≤ zpowers u
    rw [← ha]
    exact zpowers_le.mpr hau
  · exact zpowers_le.mpr huC

private theorem sq_ne_one_of_order_four {P : Type*} [Group P] {u : P}
    (hu : orderOf u = 4) : u ^ 2 ≠ 1 := by
  intro h
  have hd := orderOf_dvd_of_pow_eq_one h
  norm_num [hu] at hd

private theorem dihedral_four_nonsquare (a b : DihedralGroup 4)
    (ha : a ^ 2 ≠ 1) (hb : b ^ 2 ≠ 1) : b = a ∨ b = a⁻¹ := by
  revert a b
  decide

private theorem dihedral_of_selfcentralizing_four_inverted
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (u v : P) (hu : orderOf u = 4)
    (hC : centralizer ({u} : Set P) = zpowers u)
    (hv : v ^ 2 = 1) (hvout : v ∉ zpowers u)
    (hinv : v * u * v⁻¹ = u⁻¹) : Nonempty (P ≃* DihedralGroup 4) := by
  let H := zpowers u ⊔ zpowers v
  have huH : u ∈ H := mem_sup_left (mem_zpowers u)
  have hvH : v ∈ H := mem_sup_right (mem_zpowers v)
  have hinverts (x : P) (hx : x ∈ zpowers u) : v * x * v⁻¹ = x⁻¹ := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    change MulAut.conj v (u ^ k) = (u ^ k)⁻¹
    rw [map_zpow, MulAut.conj_apply, hinv, inv_zpow]
  have hmodel : Nonempty (H ≃* DihedralGroup 4) := by
    have hm := nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted
      (zpowers u) v inferInstance hv hvout hinverts
    rw [Nat.card_zpowers, hu] at hm
    exact hm
  obtain ⟨f⟩ := hmodel
  have hnorm : normalizer (H : Set P) = H := by
    apply le_antisymm ?_ H.le_normalizer
    intro g hg
    have hgu : g * u * g⁻¹ ∈ H := (mem_normalizer_iff.mp hg u).mp huH
    let a : H := ⟨u, huH⟩
    let b : H := ⟨g * u * g⁻¹, hgu⟩
    have ha : orderOf a = 4 := by simpa [a] using hu
    have hb : orderOf b = 4 := by
      change orderOf (⟨g * u * g⁻¹, hgu⟩ : H) = 4
      rw [orderOf_mk, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hu]
    have haf : (f a) ^ 2 ≠ 1 := sq_ne_one_of_order_four ((f.orderOf_eq a).trans ha)
    have hbf : (f b) ^ 2 ≠ 1 := sq_ne_one_of_order_four ((f.orderOf_eq b).trans hb)
    have hab : g * u * g⁻¹ = u ∨ g * u * g⁻¹ = u⁻¹ := by
      rcases dihedral_four_nonsquare (f a) (f b) haf hbf with h | h
      · exact Or.inl (congrArg Subtype.val (f.injective h))
      · exact Or.inr (congrArg Subtype.val (f.injective (h.trans (f.map_inv a).symm)))
    rcases hab with h | h
    · have hgC : g ∈ centralizer ({u} : Set P) :=
        mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h)
      exact mem_sup_left (hC ▸ hgC)
    · have hvg : v * g ∈ centralizer ({u} : Set P) := by
        apply mem_centralizer_singleton_iff.mpr
        apply mul_inv_eq_iff_eq_mul.mp
        calc
          (v * g) * u * (v * g)⁻¹ = v * (g * u * g⁻¹) * v⁻¹ := by group
          _ = v * u⁻¹ * v⁻¹ := by rw [h]
          _ = (v * u * v⁻¹)⁻¹ := by group
          _ = u := by rw [hinv, inv_inv]
      have hh := H.mul_mem (H.inv_mem hvH) (mem_sup_left (hC ▸ hvg))
      simpa using hh
  let : Group.IsNilpotent P := hP.isNilpotent
  have htop : H = ⊤ := normalizerCondition_iff_only_full_group_self_normalizing.mp
    Group.normalizerCondition_of_isNilpotent H hnorm
  exact ⟨Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr htop.symm).trans f)⟩

open scoped IsMulCommutative

private theorem inverter_of_normal_four
    {P : Type*} [Group P] [Finite P]
    (U : Subgroup P) [U.Normal] [IsElementaryAbelian 2 U] (hU : Nat.card U = 4)
    (u : P) (hu : orderOf u = 4) (huZ : u ^ 2 ∈ center P)
    [IsCyclic (centralizer ({u} : Set P))] :
    ∃ v : P, v ^ 2 = 1 ∧ v ∉ centralizer ({u} : Set P) ∧
      v * u * v⁻¹ = u⁻¹ := by
  let C := centralizer ({u} : Set P)
  obtain ⟨v, hvU, hvC⟩ := SetLike.not_le_iff_exists.mp (four_not_le_cyclic U C hU)
  let w : U := ⟨v, hvU⟩
  let f : MulAut U := MulAut.conjNormal u
  have hff (x : U) : f (f x) = x := by
    apply Subtype.ext
    change u * (u * (x : P) * u⁻¹) * u⁻¹ = x
    calc
      u * (u * (x : P) * u⁻¹) * u⁻¹ = u ^ 2 * x * (u ^ 2)⁻¹ := by simp only [pow_two]; group
      _ = x := mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp huZ x).symm
  have hinvol (x : U) : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_two] using
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 U) x))
  let d : U := f w * w⁻¹
  have hfd : f d = d := by
    dsimp [d]
    rw [map_mul, map_inv, hff, hinvol, hinvol]
    exact mul_comm _ _
  have hdC : (d : P) ∈ C := mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hfd)).symm
  have hdne : (d : P) ≠ 1 := by
    intro h
    have heq : f w = w := mul_inv_eq_one.mp (Subtype.ext h : d = 1)
    apply hvC
    exact mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val heq)).symm
  have hdorder : orderOf (d : P) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (d : P) d.property) hdne
  have hzorder : orderOf (u ^ 2) = 2 := by rw [orderOf_pow, hu]; decide
  have hzC : u ^ 2 ∈ C := pow_mem (mem_centralizer_singleton_iff.mpr rfl) 2
  have hdz : (d : P) = u ^ 2 := congrArg Subtype.val
    (IsCyclic.eq_of_orderOf_eq_two
      (x := (⟨d, hdC⟩ : C)) (y := ⟨u ^ 2, hzC⟩)
      (by simpa using hdorder) (by simpa using hzorder))
  have hv2 : v ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) v hvU
  refine ⟨v, hv2, hvC, ?_⟩
  have hd : u * v * u⁻¹ * v⁻¹ = u ^ 2 := hdz
  have h : v * u⁻¹ * v⁻¹ = u := by
    have hh := congrArg (fun x : P => u⁻¹ * x) hd
    simpa only [← mul_assoc, inv_mul_cancel, one_mul, pow_two] using hh
  calc
    v * u * v⁻¹ = (v * u⁻¹ * v⁻¹)⁻¹ := by group
    _ = u⁻¹ := by rw [h]

namespace IsPGroup

/-- A cyclic centralizer of an order-four element with central square
recognizes a two-group containing an elementary four as dihedral or semidihedral. -/
public theorem exists_dihedral_or_semidihedral_of_cyclic_centralizer_of_central_square
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (u : P) (hu : orderOf u = 4) (huZ : u ^ 2 ∈ center P)
    (hC : IsCyclic (centralizer ({u} : Set P))) :
    (∃ n : ℕ, 1 ≤ n ∧ Nonempty (P ≃* DihedralGroup (2 ^ n))) ∨
      ∃ (n : ℕ) (hn : 4 ≤ n), Nonempty (P ≃* Semidihedral.StandardModel n hn) := by
  let : IsCyclic (centralizer ({u} : Set P)) := hC
  by_cases hfour : ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4
  · obtain ⟨U, hUn, hUe, hU⟩ := hfour
    let : U.Normal := hUn
    let : IsElementaryAbelian 2 U := hUe
    have hCu := centralizer_eq_zpowers_of_normal_four hP U hU u
    obtain ⟨v, hv, hvC, hinv⟩ := inverter_of_normal_four U hU u hu huZ
    exact Or.inl ⟨2, by decide, dihedral_of_selfcentralizing_four_inverted
      hP u v hu hCu hv (hCu ▸ hvC) hinv⟩
  · rcases hP.exists_dihedral_or_semidihedral_of_no_normal_four hfour E hE with
      ⟨m, ⟨e⟩⟩ | ⟨n, hn, hcard, a, b, ha, hb, hab, hgen⟩
    · obtain ⟨n, hn⟩ := (hP.of_equiv e).exists_orderOf_eq_pow (DihedralGroup.r 1)
      rw [DihedralGroup.orderOf_r_one] at hn
      subst m
      have hcard : Nat.card P = 2 * 2 ^ n :=
        (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
      have hn1 : 1 ≤ n := by
        have hh := E.card_le_card_group
        rw [hE, hcard] at hh
        by_contra hn1
        have hn0 : n = 0 := by omega
        simp [hn0] at hh
      exact Or.inl ⟨n, hn1, ⟨e⟩⟩
    · exact Or.inr ⟨n, hn,
        Semidihedral.standardModel_equiv_of_presentation hn a b ha hb hab hgen hcard⟩

end IsPGroup
