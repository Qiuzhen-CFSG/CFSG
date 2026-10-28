module
public import Theory.GroupTheory.PGroup.LargeBinaryHallRotations
public import Theory.GroupTheory.PGroup.LargeHallRotationStructure
public import Theory.GroupTheory.PGroup.ExtraspecialCentralProduct

/-!
# Elementary central quotients or large rotations in symplectic two-groups

A finite binary symplectic two-group with cyclic center either has elementary
abelian central quotient or admits a normal cyclic rotation subgroup generated
by an element of order divisible by eight. In the latter case every square lies
in the rotation squares, the generator's centralizer has index at most two,
and centralizing its square already implies centralizing the generator.

Split the commuting extraspecial-or-trivial and Hall factors. Cyclic tails have
central squares. A small noncyclic tail is nonabelian because the ambient center
is cyclic, hence has order eight and is extraspecial; again all squares are
central. For large tails use the Hall rotation power calculations. The common
central involution puts extraspecial squares in the rotation squares. A cyclic
index-two subgroup of the tail centralizes the rotation square and therefore
the rotation itself, giving the index bound. Both centralizer assertions lift
through the commuting product. The trivial extraspecial factor is handled
explicitly in the square calculations.

Source motivation: Janko–Thompson, Math. Z. 113 (1970), result 1.1, p.385,
and its application on p.389. The Hall-factor power calculations are supplied
by the cited rotation and extraspecial central-product modules.
-/

open Subgroup
open scoped IsMulCommutative

private theorem hall_cyclic_index_two {D : Type*} [Group D] [Finite D]
    (hD : IsBinaryHallFactor D) (hnc : ¬ IsCyclic D) (hlarge : 16 ≤ Nat.card D) :
    ∃ R : Subgroup D, IsCyclic R ∧ R.index = 2 := by
  have transfer {H : Type} [Group H] (e : D ≃* H)
      (R : Subgroup H) [IsCyclic R] (hi : R.index = 2) :
      ∃ R : Subgroup D, IsCyclic R ∧ R.index = 2 := by
    refine ⟨R.map e.symm.toMonoidHom, (e.symm.subgroupMap R).isCyclic.mp inferInstance, ?_⟩
    simpa using hi
  rcases hD with hcyc | ⟨n, hn, ⟨e⟩⟩ | ⟨m, ⟨e⟩⟩ | ⟨n, hn, hc, a, b, ha, hb, hr, hg⟩
  · exact (hnc hcyc).elim
  · let m := 2 ^ (n - 2)
    let : NeZero m := ⟨by dsimp [m]; positivity⟩
    let R := zpowers (QuaternionGroup.a 1 : QuaternionGroup m)
    apply transfer e R
    have hh := R.index_mul_card
    rw [Nat.card_zpowers, QuaternionGroup.orderOf_a_one,
      Nat.card_eq_fintype_card, QuaternionGroup.card] at hh
    have hm : 0 < m := by dsimp [m]; positivity
    nlinarith
  · have hc : Nat.card D = 2 * m := (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
    let : NeZero m := ⟨by omega⟩
    let R := zpowers (DihedralGroup.r 1 : DihedralGroup m)
    apply transfer e R
    have hh := R.index_mul_card
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at hh
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < m) hh
  · refine ⟨zpowers a, inferInstance, ?_⟩
    have hh := (zpowers a).index_mul_card
    rw [Nat.card_zpowers, ha, hc] at hh
    have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
      omega
    rw [hp] at hh
    exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ (n - 1)) hh

private theorem small_factor_extraspecial
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hP : IsPGroup 2 P) (A D : Subgroup P)
    (hc : D ≤ centralizer (A : Set P)) (hg : A ⊔ D = ⊤)
    (hnc : ¬ IsCyclic D) (hsmall : Nat.card D < 16) : IsExtraspecial 2 D := by
  have hnonab := noncommutative_factor_of_noncyclic_of_cyclic_center A D hc hg hnc
  obtain ⟨k, hk⟩ := (hP.to_subgroup D).exists_card_eq
  have hklt : k < 4 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (hk ▸ hsmall)
  have hcard : Nat.card D = 8 := by
    interval_cases k
    · exact (hnc (isCyclic_of_card_dvd_prime (p := 2) (by rw [hk]; decide))).elim
    · exact (hnc (isCyclic_of_card_dvd_prime (p := 2) (by rw [hk]; decide))).elim
    · exact (hnonab (IsPGroup.isMulCommutative_of_card_eq_prime_sq hk)).elim
    · exact hk
  exact IsExtraspecial.of_noncommutative_card_eight hcard hnonab

private theorem center_factor_le_center
    {P : Type*} [Group P] (A D : Subgroup P) [D.Normal]
    (hc : D ≤ centralizer (A : Set P)) (hg : A ⊔ D = ⊤)
    (y : D) (hy : y ∈ center D) : (y : P) ∈ center P := by
  apply mem_center_iff.mpr
  intro p
  obtain ⟨a, ha, d, hd, rfl⟩ := mem_sup_of_normal_right.mp (hg.symm ▸ mem_top p)
  have hya : Commute a (y : P) := hc y.property a ha
  have hyd : Commute d (y : P) := congrArg Subtype.val (mem_center_iff.mp hy ⟨d, hd⟩)
  exact (hya.mul_left hyd).eq

private theorem elementary_central_quotient_of_squares
    {P : Type*} [Group P] (hsq : ∀ x : P, x ^ 2 ∈ center P) :
    IsElementaryAbelian 2 (P ⧸ center P) := by
  have hpow (x : P ⧸ center P) : x ^ 2 = 1 := by
    induction x using QuotientGroup.induction_on with
    | H x => exact (QuotientGroup.eq_one_iff _).mpr (hsq x)
  have hinv (x : P ⧸ center P) : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hpow x)
  refine {
    toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  calc
    x * y = (x * y)⁻¹ := (hinv _).symm
    _ = y * x := by rw [mul_inv_rev, hinv, hinv]

private theorem tail_rotation_index {D : Type*} [Group D] [Finite D]
    (hD : IsBinaryHallFactor D) (hnc : ¬ IsCyclic D) (hlarge : 16 ≤ Nat.card D)
    (r : D) (hcent : centralizer ({r ^ 2} : Set D) ≤ zpowers r) :
    (centralizer ({r} : Set D)).index ∣ 2 := by
  obtain ⟨R, hRc, hi⟩ := hall_cyclic_index_two hD hnc hlarge
  let : IsCyclic R := hRc
  have hr2 : r ^ 2 ∈ R := R.sq_mem_of_index_two hi r
  have hRC : R ≤ centralizer ({r} : Set D) := by
    intro x hx
    have hxrot : x ∈ zpowers r := hcent (by
      intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact R.le_centralizer hx _ hr2)
    exact mem_centralizer_singleton_iff.mpr
      ((zpowers r).le_centralizer hxrot r (mem_zpowers r)).symm
  simpa only [hi] using index_dvd_of_le hRC

private theorem lift_rotation_centralizers
    {P : Type*} [Group P] [Finite P]
    (A D : Subgroup P) [D.Normal]
    (hc : D ≤ centralizer (A : Set P)) (hg : A ⊔ D = ⊤)
    (r : D) (hcent : centralizer ({r ^ 2} : Set D) ≤ zpowers r)
    (hi : (centralizer ({r} : Set D)).index ∣ 2) :
    (centralizer ({(r : P)} : Set P)).index ≤ 2 ∧
    centralizer ({(r : P) ^ 2} : Set P) ≤ centralizer ({(r : P)} : Set P) := by
  let C := centralizer ({(r : P)} : Set P)
  have hAC : A ≤ C := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hc r.property a ha)
  have hDC (d : D) (hd : d ∈ centralizer ({r} : Set D)) : (d : P) ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hd)
  constructor
  · apply Nat.le_of_dvd (by decide : 0 < 2)
    apply index_dvd_two_iff.mpr
    obtain ⟨t, ht⟩ := index_dvd_two_iff.mp hi
    refine ⟨(t : P), ?_⟩
    intro x
    obtain ⟨a, ha, d, hd, rfl⟩ := mem_sup_of_normal_right.mp (hg.symm ▸ mem_top x)
    rcases ht (⟨d, hd⟩ : D) with h | h
    · left
      simpa only [coe_mul, mul_assoc] using C.mul_mem (hAC ha) (hDC _ h)
    · right
      exact C.mul_mem (hAC ha) (hDC _ h)
  · intro x hx
    obtain ⟨a, ha, d, hd, rfl⟩ := mem_sup_of_normal_right.mp (hg.symm ▸ mem_top x)
    have hdC : (⟨d, hd⟩ : D) ∈ centralizer ({r ^ 2} : Set D) := by
      apply mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      change d * (r : P) ^ 2 = (r : P) ^ 2 * d
      apply mul_left_cancel (a := a)
      calc
        a * (d * (r : P) ^ 2) = (a * d) * (r : P) ^ 2 := (mul_assoc _ _ _).symm
        _ = (r : P) ^ 2 * (a * d) := (hx _ (Set.mem_singleton _)).symm
        _ = a * ((r : P) ^ 2 * d) := by
          rw [← mul_assoc, ← hc (D.pow_mem r.property 2) a ha, mul_assoc]
    apply C.mul_mem (hAC ha)
    apply hDC ⟨d, hd⟩
    exact mem_centralizer_singleton_iff.mpr
      ((zpowers r).le_centralizer (hcent hdC) r (mem_zpowers r)).symm

private theorem lift_rotation_squares
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hP : IsPGroup 2 P) (A D : Subgroup P) [A.Normal] [D.Normal]
    (hA : A = ⊥ ∨ IsExtraspecial 2 A)
    (hc : D ≤ centralizer (A : Set P)) (hg : A ⊔ D = ⊤)
    (r : D) (hr8 : 8 ∣ orderOf r)
    (hsq : ∀ d : D, d ^ 2 ∈ zpowers (r ^ 2))
    (hZ : center D ≤ zpowers (r ^ 2)) :
    ∀ x : P, x ^ 2 ∈ zpowers ((r : P) ^ 2) := by
  have hmap : (zpowers (r ^ 2)).map D.subtype = zpowers ((r : P) ^ 2) := by
    rw [MonoidHom.map_zpowers]
    rfl
  have haSq (a : A) : (a : P) ^ 2 ∈ zpowers ((r : P) ^ 2) := by
    rcases hA with hAbot | hA
    · have ha1 : (a : P) = 1 := by simpa [hAbot] using a.property
      simp [ha1]
    · let : IsExtraspecial 2 A := hA
      have hD : D ≠ ⊥ := by
        intro h
        have hr1 : (r : P) = 1 := by simpa [h] using r.property
        have hr1' : r = 1 := Subtype.ext hr1
        simp [hr1'] at hr8
      have hinf : A ⊓ D = (center A).map A.subtype := by
        apply eq_of_le_of_card_ge
        · intro x hx
          exact ⟨⟨x, hx.1⟩, mem_center_iff.mpr
            (fun b => Subtype.ext (hc hx.2 b b.property)), rfl⟩
        · rw [card_map_of_injective A.subtype_injective,
            IsExtraspecial.center_order_p 2 A,
            card_inf_eq_two_of_extraspecial_of_cyclic_center hP A D hD hc]
      have ha : (a : P) ^ 2 ∈ A ⊓ D := by
        rw [hinf]
        exact ⟨a ^ 2, IsExtraspecial.square_mem_center a, rfl⟩
      have hz : (⟨(a : P) ^ 2, ha.2⟩ : D) ∈ center D :=
        mem_center_iff.mpr (fun d => Subtype.ext (hc d.property _ ha.1).symm)
      rw [← hmap]
      exact ⟨⟨(a : P) ^ 2, ha.2⟩, hZ hz, rfl⟩
  intro x
  obtain ⟨a, ha, d, hd, rfl⟩ := mem_sup_of_normal_right.mp (hg.symm ▸ mem_top x)
  rw [(show Commute a d from hc hd a ha).mul_pow]
  apply mul_mem (haSq ⟨a, ha⟩)
  rw [← hmap]
  exact ⟨(⟨d, hd⟩ : D) ^ 2, hsq ⟨d, hd⟩, rfl⟩

/-- A binary symplectic two-group with cyclic center has elementary central
quotient, or has a large normal rotation containing every square in its square
subgroup, with centralizer of index at most two and unchanged by squaring. -/
public theorem IsBinarySymplecticType.elementary_central_quotient_or_large_rotation
    {Q : Type*} [Group Q] [Finite Q] [IsCyclic (center Q)]
    (hQ : IsPGroup 2 Q) (hsymp : IsBinarySymplecticType Q) :
    IsElementaryAbelian 2 (Q ⧸ center Q) ∨
      ∃ r : Q, 8 ∣ orderOf r ∧ (zpowers r).Normal ∧
        (centralizer ({r} : Set Q)).index ≤ 2 ∧
        (∀ x : Q, x ^ 2 ∈ zpowers (r ^ 2)) ∧
        centralizer ({r ^ 2} : Set Q) ≤ centralizer ({r} : Set Q) := by
  obtain ⟨A, D, hAn, hDn, hA, hD, hc, hg⟩ := hsymp.exists_normal_factors
  let : A.Normal := hAn
  let : D.Normal := hDn
  have hAsq (a : A) : a ^ 2 ∈ center A := by
    rcases hA with hAbot | hA
    · have ha1 : a = 1 := Subtype.ext (by simpa [hAbot] using a.property)
      simp [ha1]
    · let : IsExtraspecial 2 A := hA
      exact IsExtraspecial.square_mem_center a
  have elementary (hDsq : ∀ d : D, d ^ 2 ∈ center D) :
      IsElementaryAbelian 2 (Q ⧸ center Q) := by
    apply elementary_central_quotient_of_squares
    intro x
    obtain ⟨a, ha, d, hd, rfl⟩ := mem_sup_of_normal_right.mp (hg.symm ▸ mem_top x)
    rw [(show Commute a d from hc hd a ha).mul_pow]
    exact (center Q).mul_mem
      (center_factor_le_center D A (le_centralizer_iff.mp hc) (sup_comm A D ▸ hg)
        ((⟨a, ha⟩ : A) ^ 2) (hAsq _))
      (center_factor_le_center A D hc hg ((⟨d, hd⟩ : D) ^ 2) (hDsq _))
  by_cases hcyc : IsCyclic D
  · left
    let : IsCyclic D := hcyc
    apply elementary
    intro d
    rw [center_eq_top]
    trivial
  by_cases hlarge : 16 ≤ Nat.card D
  · right
    obtain ⟨r, hr8, hsq, hZ, hcent, _⟩ :=
      hD.exists_large_rotation (hQ.to_subgroup D) hcyc hlarge
    let : (zpowers r).Characteristic :=
      characteristic_zpowers_of_squares_and_centralizer r hsq hcent
    have hrnormal : (zpowers (r : Q)).Normal := by
      have hm : (zpowers r).map D.subtype = zpowers (r : Q) := MonoidHom.map_zpowers _ _
      rw [← hm]
      infer_instance
    obtain ⟨hi, hcs⟩ := lift_rotation_centralizers A D hc hg r hcent
      (tail_rotation_index hD hcyc hlarge r hcent)
    exact ⟨r, by simpa only [orderOf_coe] using hr8, hrnormal, hi,
      lift_rotation_squares hQ A D hA hc hg r hr8 hsq hZ, hcs⟩
  · left
    let : IsExtraspecial 2 D := small_factor_extraspecial hQ A D hc hg hcyc (by omega)
    exact elementary IsExtraspecial.square_mem_center
