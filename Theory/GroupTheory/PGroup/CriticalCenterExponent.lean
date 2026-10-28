module

public import Theory.GroupTheory.PGroup.UniqueNormalFourCriticalCenter
public import Theory.GroupTheory.PGroup.CentralInvolutionRoots
public import Theory.GroupTheory.HomocyclicSylowCentralizers

/-!
# Elementary centers of critical subgroups with three involutions

Let C be a nonabelian critical subgroup of a finite two-group P, with
central omega of P of order two, central omega of C of order four, and
every involution of C central in C. If Aut(P) is not a two-group, then
the center of C is elementary abelian.

The elementary central quotient makes every commutator an involution. Since
the derived subgroup of C is central in P, it has order two. Its unique
involution is fixed by every automorphism of C. The action on the rank-two
abelian center is thus a two-group: the Frattini action has order dividing
six, and any order-three automorphism of the center would be fixed-point-free.

If the center had a nontrivial square, its square subgroup, normal in P,
would contain the unique central involution of P, hence every commutator
of C. Correcting squares by these central roots shows that an automorphism
fixing the center also fixes the central quotient. The paired-action kernel
is a two-group, so all of Aut(C) would be a two-group. Critical-subgroup
automorphism detection contradicts the hypothesis on Aut(P).

Source context: Thompson's critical subgroup theorem, Gorenstein, *Finite
Groups*, Theorem 5.3.11; Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3,
printed p.386; MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3. The argument uses intrinsic
automorphisms and does not turn ambient fusion into automorphisms of C.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

private theorem fixed_point_aut_subgroup_two
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    (hA : IsPGroup 2 A) (hfour : Nat.card (omega₁ A (p := 2)) = 4)
    (H : Subgroup (MulAut A)) (z : A) (hz : z ≠ 1)
    (hfix : ∀ a ∈ H, a z = z) : IsPGroup 2 H := by
  let : IsKleinFour (A ⧸ frattini A) :=
    hA.isKleinFour_frattini_quotient_of_card_omega_one_eq_four hfour
  let q := (quotientAut (frattini A)).comp H.subtype
  have hk : IsPGroup 2 q.ker :=
    (isPGroup_quotientAut_frattini_kernel hA).comap_of_injective H.subtype H.subtype_injective
  have hr : IsPGroup 2 q.range := by
    have hd : Nat.card q.range ∣ 6 := by
      rw [← IsKleinFour.card_mulAut (A ⧸ frattini A)]
      exact card_subgroup_dvd_card _
    have h3 : ¬ 3 ∣ Nat.card H := by
      intro h
      obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 h
      exact hz ((a : MulAut A).fixed_point_eq_one_of_order_three_of_kleinFour_frattini
        hA ((orderOf_coe a).trans ha) z (hfix a a.property))
    have hle := Nat.le_of_dvd (by decide : 0 < 6) hd
    have hn3 : ¬ 3 ∣ Nat.card q.range := fun h => h3 (h.trans (card_range_dvd q))
    have hpos : 0 < Nat.card q.range := Nat.card_pos
    have he : Nat.card q.range = 1 ∨ Nat.card q.range = 2 := by
      interval_cases Nat.card q.range <;> omega
    rcases he with h | h
    · exact IsPGroup.of_card (n := 0) h
    · exact IsPGroup.of_card (n := 1) h
  have ht := hr.comap_of_ker_isPGroup q hk
  rw [MonoidHom.comap_range_self] at ht
  exact ht.of_equiv topEquiv

private theorem square_mul_of_central_squares
    {P : Type*} [Group P]
    (hclass : commutator P ≤ center P)
    (hsq : ∀ x : P, x ^ 2 ∈ center P) (x y : P) :
    (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅x,y⁆ := by
  have hc : ⁅x,y⁆ ∈ center P :=
    hclass (commutator_mem_commutator (mem_top x) (mem_top y))
  symm
  calc
    x ^ 2 * y ^ 2 * ⁅x,y⁆ = ⁅x,y⁆ * (x ^ 2 * y ^ 2) := mem_center_iff.mp hc _
    _ = x * y * x⁻¹ * (y⁻¹ * x ^ 2) * y ^ 2 := by
      simp only [commutatorElement_def, mul_assoc]
    _ = x * y * x⁻¹ * (x ^ 2 * y⁻¹) * y ^ 2 := by rw [mem_center_iff.mp (hsq x)]
    _ = (x * y) ^ 2 := by simp only [pow_two]; group

private theorem center_kernel_two_of_roots
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hclass : commutator P ≤ center P)
    (hsq : ∀ x : P, x ^ 2 ∈ center P)
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hroots : ∀ x y : P, ∃ z : center P, (z : P) ^ 2 = ⁅x,y⁆) :
    IsPGroup 2 (MulAut.characteristic (center P)).ker := by
  have hle : (MulAut.characteristic (center P)).ker ≤ (automorphismPair (center P)).ker := by
    intro a ha
    have hfix (z : center P) : a (z : P) = z :=
      congrArg Subtype.val (DFunLike.congr_fun ha z)
    change automorphismPair (center P) a = 1
    rw [automorphismPair_apply]
    refine Prod.ext ha ?_
    apply MulEquiv.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center P) q
    rw [quotientAut_apply_mk]
    apply Eq.symm
    apply QuotientGroup.eq.mpr
    obtain ⟨z, hz⟩ := hroots x⁻¹ (a x)
    have hh : (x⁻¹ * a x) ^ 2 = (z : P) ^ 2 := by
      rw [square_mul_of_central_squares hclass hsq, inv_pow, ← map_pow,
        hfix ⟨x ^ 2, hsq x⟩, inv_mul_cancel, one_mul, hz]
    exact IsPGroup.mem_center_of_square_eq_central_square hcentral _ z hh
  exact (isPGroup_automorphism_pair_kernel (center P) (hP.to_subgroup _)).to_le hle

private theorem central_square_one_mem_normal
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (N : Subgroup P) [N.Normal] (hne : N ≠ ⊥)
    (x : P) (hx : x ∈ center P) (hx2 : x ^ 2 = 1) : x ∈ N := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : Nontrivial N := (nontrivial_iff_ne_bot N).mpr hne
  obtain ⟨K, _, hKN, hK, hKZ⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) N inferInstance
  let O := (omega₁ (center P) (p := 2)).map (center P).subtype
  have hKO : K ≤ O := by
    intro k hk
    refine ⟨⟨k, hKZ hk⟩, subset_closure ?_, rfl⟩
    change (⟨k, hKZ hk⟩ : center P)^2 = 1
    apply Subtype.ext
    exact congrArg (fun t : K => (t : P)) (show (⟨k, hk⟩ : K)^2 = 1 by
      simpa only [hK] using pow_card_eq_one' (x := (⟨k, hk⟩ : K)))
  have hKOeq : K = O := eq_of_le_of_card_ge hKO (by
    rw [card_map_of_injective (center P).subtype_injective, hZ, hK])
  apply hKN
  rw [hKOeq]
  exact ⟨⟨x, hx⟩, subset_closure (Subtype.ext hx2), rfl⟩

private theorem critical_commutators_have_central_roots
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C)
    (hne : ∃ z : center C, z ^ 2 ≠ 1) :
    ∀ x y : C, ∃ z : center C, (z : C) ^ 2 = ⁅x,y⁆ := by
  let : C.Characteristic := hC.characteristic
  let Z := center C
  let D := (powMonoidHom 2 : Z →* Z).range
  let : D.Characteristic := by
    rw [characteristic_iff_map_eq]
    intro a
    ext z
    constructor
    · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
      exact ⟨a w, (map_pow a w 2).symm⟩
    · rintro ⟨w, rfl⟩
      exact ⟨(a.symm w)^2, ⟨a.symm w, rfl⟩, by simp⟩
  let N := (D.map Z.subtype).map C.subtype
  let : N.Normal := inferInstance
  have hN : N ≠ ⊥ := by
    obtain ⟨z, hz⟩ := hne
    intro hbot
    have hm : ((z^2 : Z) : C) ∈ D.map Z.subtype :=
      mem_map_of_mem Z.subtype (show z^2 ∈ D from ⟨z, rfl⟩)
    have hm' : (((z^2 : Z) : C) : P) ∈ N := mem_map_of_mem C.subtype hm
    rw [hbot, mem_bot] at hm'
    exact hz (Subtype.ext (Subtype.ext hm'))
  have hsq (x : C) : x ^ 2 ∈ center C := by
    let : IsElementaryAbelian 2 (C ⧸ center C) := hC.quotient_elementary
    apply (QuotientGroup.eq_one_iff (N := center C) _).mp
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (C ⧸ center C))
      (QuotientGroup.mk' (center C) x)
  intro x y
  have hcP : (⁅x,y⁆ : C).val ∈ center P :=
    hC.commutator_self_le_ambient_center (commutator_mem_commutator x.property y.property)
  have hc : ⁅x,y⁆ ∈ center C := mem_center_iff.mpr
    (fun z => Subtype.ext (mem_center_iff.mp hcP z))
  have hc2 : ⁅x,y⁆ ^ 2 = 1 := by
    have hh : ⁅x ^ 2,y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_center_iff.mp (hsq x) y).symm
    rwa [pow_two, commutatorElement_mul_left_eq_conj_mul,
      mem_center_iff.mp hc x, mul_inv_cancel_right, ← pow_two] at hh
  have hm := central_square_one_mem_normal hP hZ N hN (⁅x,y⁆ : C).val hcP
    (congrArg Subtype.val hc2)
  obtain ⟨c, ⟨z, ⟨w, hw⟩, hzc⟩, hcx⟩ := hm
  refine ⟨w, ?_⟩
  apply Subtype.ext
  exact (congrArg (fun t : Z => ((t : C) : P)) hw).trans
    ((congrArg Subtype.val hzc).trans hcx)

/-- A nonabelian critical subgroup has derived subgroup of order two when
first omega of the ambient center has order two. -/
public theorem IsCriticalPSubgroup.card_commutator_eq_two_of_omega_ambient_center_two
    {P : Type*} [Group P] [Finite P]
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C)
    (hnonab : ¬ IsMulCommutative C) : Nat.card (commutator C) = 2 := by
  have hsq (x : C) : x ^ 2 ∈ center C := by
    let : IsElementaryAbelian 2 (C ⧸ center C) := hC.quotient_elementary
    apply (QuotientGroup.eq_one_iff (N := center C) _).mp
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (C ⧸ center C))
      (QuotientGroup.mk' (center C) x)
  let O := (omega₁ (center P) (p := 2)).map (center P).subtype
  have hle : (commutator C).map C.subtype ≤ O := by
    rw [map_le_iff_le_comap]
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    have hcP : (⁅x,y⁆ : C).val ∈ center P :=
      hC.commutator_self_le_ambient_center (commutator_mem_commutator x.property y.property)
    have hc : ⁅x,y⁆ ∈ center C := mem_center_iff.mpr
      (fun z => Subtype.ext (mem_center_iff.mp hcP z))
    have hc2 : ⁅x,y⁆ ^ 2 = 1 := by
      have hh : ⁅x ^ 2,y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_center_iff.mp (hsq x) y).symm
      rwa [pow_two, commutatorElement_mul_left_eq_conj_mul,
        mem_center_iff.mp hc x, mul_inv_cancel_right, ← pow_two] at hh
    refine ⟨⟨(⁅x,y⁆ : C).val, hcP⟩, Subgroup.subset_closure ?_, rfl⟩
    change (⟨(⁅x,y⁆ : C).val, hcP⟩ : center P)^2 = 1
    apply Subtype.ext
    exact congrArg (fun t : C => (t : P)) hc2
  have hupp := card_le_of_le hle
  change Nat.card ((commutator C).map C.subtype) ≤
    Nat.card ((omega₁ (center P) (p := 2)).map (center P).subtype) at hupp
  rw [card_map_of_injective C.subtype_injective,
    card_map_of_injective (center P).subtype_injective, hZ] at hupp
  have hne : commutator C ≠ ⊥ := fun h => hnonab ((commutator_eq_bot_iff C).mp h)
  have hn1 : Nat.card (commutator C) ≠ 1 := fun h => hne (card_eq_one.mp h)
  have hpos : 0 < Nat.card (commutator C) := Nat.card_pos
  omega

private theorem center_action_two_of_derived_two
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hclass : commutator P ≤ center P)
    (hfour : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (hD : Nat.card (commutator P) = 2) :
    IsPGroup 2 (MulAut.characteristic (center P)).range := by
  obtain ⟨d, hd, huniq⟩ := (Nat.card_eq_two_iff' (1 : commutator P)).mp hD
  let z : center P := ⟨d, hclass d.property⟩
  apply fixed_point_aut_subgroup_two (hP.to_subgroup _) hfour _ z
    (fun h => hd (Subtype.ext (congrArg (fun t : center P => (t : P)) h)))
  rintro b ⟨a, rfl⟩
  have had : MulAut.characteristic (commutator P) a d ≠ 1 := by
    intro h
    exact hd ((MulAut.characteristic (commutator P) a).injective
      (h.trans (map_one _).symm))
  apply Subtype.ext
  exact congrArg (fun t : commutator P => (t : P)) (huniq _ had)

/-- A critical subgroup with central involutions and center omega four has
an elementary center in the ambient central-two, non-two-automorphism case. -/
public theorem IsCriticalPSubgroup.center_elementary_of_omega_ambient_center_two_of_not_isPGroup_mulAut
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hAut : ¬ IsPGroup 2 (MulAut P))
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C)
    (hnonab : ¬ IsMulCommutative C)
    (hfour : Nat.card (omega₁ (center C) (p := 2)) = 4)
    (hcentral : ∀ x : C, x ^ 2 = 1 → x ∈ center C) :
    IsElementaryAbelian 2 (center C) := by
  have hpow : ∀ z : center C, z ^ 2 = 1 := by
    by_contra! hne
    have hclass : commutator C ≤ center C := by
      let : IsElementaryAbelian 2 (C ⧸ center C) := hC.quotient_elementary
      exact Normal.quotient_commutative_iff_commutator_le.mp inferInstance
    have hsq (x : C) : x ^ 2 ∈ center C := by
      let : IsElementaryAbelian 2 (C ⧸ center C) := hC.quotient_elementary
      apply (QuotientGroup.eq_one_iff (N := center C) _).mp
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (C ⧸ center C))
        (QuotientGroup.mk' (center C) x)
    have hk := center_kernel_two_of_roots (hP.to_subgroup C) hclass hsq hcentral
      (critical_commutators_have_central_roots hP hZ hC hne)
    have hr := center_action_two_of_derived_two (hP.to_subgroup C) hclass hfour
      (IsCriticalPSubgroup.card_commutator_eq_two_of_omega_ambient_center_two hZ hC hnonab)
    have ht := hr.comap_of_ker_isPGroup (MulAut.characteristic (center C)) hk
    rw [MonoidHom.comap_range_self] at ht
    exact hC.not_isPGroup_mulAut_of_ambient hP hAut (ht.of_equiv topEquiv)
  exact { toIsMulCommutative := inferInstance
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
