module

public import Theory.GroupTheory.PGroup.UniqueInvolution
public import Theory.GroupTheory.CyclicIndexTwoElementary
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Dihedral factors commuting with a unique-involution group

The binary weak-core argument following GLS2, Proposition 22.4 uses a
commuting product of a dihedral group and a two-group with a unique
involution. The shared involution is essential: a direct product of a
dihedral group with a group of order two can have elementary rank three.

For a shared involution, an elementary subgroup containing a reflection
component lies in the dihedral factor. Otherwise all components are
rotations. Their centralizer components generate an abelian, hence cyclic,
subgroup of the unique-involution factor; two cyclic factors give rank at
most two. No quaternion classification is needed.
-/

namespace Subgroup

private theorem factor_of_mem_sup {G : Type*} [Group G]
    {R C : Subgroup G} (hC : C ≤ centralizer (R : Set G))
    {x : G} (hx : x ∈ R ⊔ C) : ∃ r ∈ R, ∃ c ∈ C, r * c = x := by
  have h := coe_mul_of_right_le_normalizer_left R C
    (hC.trans (centralizer_le_normalizer _))
  rw [← SetLike.mem_coe, h] at hx
  exact hx

private theorem commutative_sup {G : Type*} [Group G]
    (R B : Subgroup G) [IsMulCommutative R] [IsMulCommutative B]
    (hBR : B ≤ centralizer (R : Set G)) : IsMulCommutative (R ⊔ B : Subgroup G) := by
  apply le_centralizer_iff_isMulCommutative.mp
  apply sup_le
  · exact le_centralizer_iff.mpr (sup_le R.le_centralizer hBR)
  · exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hBR) B.le_centralizer)

/-- An elementary binary subgroup of a commuting product of two cyclic
subgroups has order at most four. -/
public theorem card_elementary_le_four_of_cyclic_sup
    {G : Type*} [Group G] [Finite G] (R C B : Subgroup G)
    [IsCyclic R] [IsCyclic C] [IsElementaryAbelian 2 B]
    (hC : C ≤ centralizer (R : Set G)) (hB : B ≤ R ⊔ C) : Nat.card B ≤ 4 := by
  let D := C ⊔ R
  have hCD : C ≤ normalizer (R : Set G) := hC.trans (centralizer_le_normalizer _)
  let : (R.subgroupOf D).Normal := normal_subgroupOf_sup_of_le_normalizer hCD
  let : (R.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer hCD
  let : IsCyclic (C ⧸ R.subgroupOf C) := isCyclic_of_surjective
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient C R hCD
  let : IsCyclic (D ⧸ R.subgroupOf D) := isCyclic_of_surjective e e.surjective
  have hBD : B ≤ D := by simpa only [D, sup_comm] using hB
  let f : B →* D ⧸ R.subgroupOf D :=
    (QuotientGroup.mk' _).comp (inclusion hBD)
  have hrange : Nat.card f.range ≤ 2 := by
    have hexp : Monoid.exponent f.range ∣ 2 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
        rintro ⟨_, x, rfl⟩
        apply Subtype.ext
        change f x ^ 2 = 1
        rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 B) x, map_one])
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd (by decide) hexp
  have hkerR : f.ker.map B.subtype ≤ R := by
    rintro _ ⟨b, hb, rfl⟩
    exact (QuotientGroup.eq_one_iff (N := R.subgroupOf D) (inclusion hBD b)).mp hb
  let : IsCyclic (f.ker.map B.subtype) := isCyclic_of_le hkerR
  let ek := f.ker.equivMapOfInjective B.subtype B.subtype_injective
  let : IsCyclic f.ker := isCyclic_of_injective ek.toMonoidHom ek.injective
  have hker : Nat.card f.ker ≤ 2 := by
    have hexp : Monoid.exponent f.ker ∣ 2 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => Subtype.ext
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 B) x))
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd (by decide) hexp
  have hc := f.ker.card_mul_index
  rw [index_ker] at hc
  nlinarith

/-- The rotation case: the first factor need only be cyclic. -/
public theorem card_elementary_le_four_of_cyclic_unique_involution_sup
    {G : Type*} [Group G] [Finite G] (R C B : Subgroup G)
    [IsCyclic R] [IsElementaryAbelian 2 B]
    (hCtwo : IsPGroup 2 C) (hunique : ∃! z : C, orderOf z = 2)
    (hC : C ≤ centralizer (R : Set G)) (hB : B ≤ R ⊔ C) : Nat.card B ≤ 4 := by
  have hBR : B ≤ centralizer (R : Set G) :=
    hB.trans (sup_le R.le_centralizer hC)
  let D := C ⊓ (R ⊔ B)
  let : IsMulCommutative (R ⊔ B : Subgroup G) := commutative_sup R B hBR
  let : IsMulCommutative D := le_centralizer_iff_isMulCommutative.mp
    (show D ≤ centralizer (D : Set G) from
      inf_le_right.trans ((R ⊔ B).le_centralizer.trans (centralizer_le inf_le_right)))
  let : IsMulCommutative (D.subgroupOf C) := inferInstance
  let : IsCyclic (D.subgroupOf C) :=
    hCtwo.isCyclic_abelian_subgroup_of_unique_involution hunique _
  let : IsCyclic D := isCyclic_of_surjective
    (subgroupOfEquivOfLe (show D ≤ C from inf_le_left)) (MulEquiv.surjective _)
  apply card_elementary_le_four_of_cyclic_sup R D B (inf_le_left.trans hC)
  intro b hb
  obtain ⟨r, hr, c, hc, heq⟩ := factor_of_mem_sup hC (hB hb)
  have hcRB : c ∈ R ⊔ B := by
    have : c = r⁻¹ * b := by rw [← heq]; simp
    rw [this]
    exact (R ⊔ B).mul_mem ((R ⊔ B).inv_mem ((le_sup_left : R ≤ R ⊔ B) hr))
      ((le_sup_right : B ≤ R ⊔ B) hb)
  rw [← heq]
  exact (R ⊔ D).mul_mem ((le_sup_left : R ≤ R ⊔ D) hr)
    ((le_sup_right : D ≤ R ⊔ D) ⟨hc, hcRB⟩)

private theorem square_one_factor {G : Type*} [Group G] {q c : G}
    (hcomm : Commute q c) (hqc : (q * c) ^ 2 = 1) (hq : q ^ 2 = 1) :
    c ^ 2 = 1 := by
  simpa only [hcomm.mul_pow, hq, one_mul] using hqc

/-- A reflection outside the cyclic part forces an elementary subgroup
back into the first factor, when all involutions of the second factor
already lie in the first. -/
public theorem elementary_le_of_involutory_complement
    {G : Type*} [Group G] (Q R C B : Subgroup G)
    [IsElementaryAbelian 2 B]
    (hC : C ≤ centralizer (Q : Set G)) (hB : B ≤ Q ⊔ C)
    (hCin : ∀ c ∈ C, c ^ 2 = 1 → c ∈ Q)
    (hout : ∀ q ∈ Q, q ∉ R → q ^ 2 = 1)
    (hcent : ∀ b ∈ Q, b ∉ R → ∀ q ∈ Q, Commute q b → q ^ 2 = 1)
    (hnot : ¬ B ≤ R ⊔ C) : B ≤ Q := by
  obtain ⟨b, hb, hbout⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨q, hq, c, hc, hqc⟩ := factor_of_mem_sup hC (hB hb)
  have hqout : q ∉ R := by
    intro hqR
    exact hbout (hqc ▸ (R ⊔ C).mul_mem
      ((le_sup_left : R ≤ R ⊔ C) hqR) ((le_sup_right : C ≤ R ⊔ C) hc))
  have hc2 : c ^ 2 = 1 := square_one_factor (hC hc q hq)
    (hqc ▸ elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb)
    (hout q hq hqout)
  have hbQ : b ∈ Q := hqc ▸ Q.mul_mem hq (hCin c hc hc2)
  have hbR : b ∉ R := fun h => hbout ((le_sup_left : R ≤ R ⊔ C) h)
  intro x hx
  obtain ⟨a, ha, d, hd, had⟩ := factor_of_mem_sup hC (hB hx)
  have hxb : Commute (a * d) b := by
    rw [had]
    exact (B.le_centralizer hb x hx)
  have hab : Commute a b := by
    have hdb : Commute d b := (hC hd b hbQ).symm
    have heq : (a * b) * d = (b * a) * d := calc
      a * b * d = a * (d * b) := by rw [hdb.eq, mul_assoc]
      _ = b * a * d := by rw [← mul_assoc, hxb.eq, mul_assoc]
    exact mul_right_cancel heq
  have ha2 := hcent b hbQ hbR a ha hab
  have hd2 : d ^ 2 = 1 := square_one_factor (hC hd a ha)
    (had ▸ elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx) ha2
  exact had ▸ Q.mul_mem ha (hCin d hd hd2)

end Subgroup

namespace DihedralGroup

private theorem square_eq_one_of_commute_reflection {n : ℕ}
    (x : DihedralGroup n) (i : ZMod n) (h : Commute x (sr i)) : x ^ 2 = 1 := by
  cases x with
  | r j =>
    have heq : i - j = i + j := by simpa only [Commute, SemiconjBy,
      r_mul_sr, sr_mul_r, sr.injEq] using h
    have hj : j + j = 0 := by linear_combination -heq
    simp [pow_two, hj]
  | sr j => simp [pow_two]

/-- Every subgroup of a finite dihedral group whose elements square to
one has order at most four, including the parameters one and two. -/
public theorem card_le_four_of_square_eq_one {n : ℕ} [NeZero n]
    (E : Subgroup (DihedralGroup n)) (hE : ∀ x : E, x ^ 2 = 1) : Nat.card E ≤ 4 := by
  have hc := (Subgroup.zpowers (r 1 : DihedralGroup n)).index_mul_card
  rw [Nat.card_zpowers, orderOf_r_one, nat_card] at hc
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hi : (Subgroup.zpowers (r 1 : DihedralGroup n)).index = 2 := by nlinarith
  exact Subgroup.card_le_four_of_pow_two_of_cyclic_index_two _ hi E hE

end DihedralGroup

namespace Subgroup

/-- A dihedral factor commuting with a two-group with a unique involution
has binary elementary rank at most two, provided the involution is shared. -/
public theorem card_elementary_le_four_of_dihedral_unique_involution_sup
    {G : Type*} [Group G] [Finite G] (Q C B : Subgroup G)
    {n : ℕ} [NeZero n] (e : Q ≃* DihedralGroup n)
    [IsElementaryAbelian 2 B] (hCtwo : IsPGroup 2 C)
    (hunique : ∃! z : C, orderOf z = 2)
    (hoverlap : ∃ z : C, orderOf z = 2 ∧ (z : G) ∈ Q)
    (hC : C ≤ centralizer (Q : Set G)) (hB : B ≤ Q ⊔ C) : Nat.card B ≤ 4 := by
  let Rq := zpowers (e.symm (DihedralGroup.r 1))
  let R := Rq.map Q.subtype
  have hRQ : R ≤ Q := map_subtype_le Rq
  have hrot (q : Q) : q ∈ Rq ↔ ∃ i, e q = DihedralGroup.r i := by
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨(k : ZMod n), ?_⟩
      rw [← hk, map_zpow, e.apply_symm_apply, DihedralGroup.r_one_zpow]
    · rintro ⟨i, hi⟩
      refine ⟨(i.val : ℤ), ?_⟩
      apply e.injective
      rw [map_zpow, e.apply_symm_apply, DihedralGroup.r_one_zpow, hi]
      simp
  have hmem (q : Q) : (q : G) ∈ R ↔ q ∈ Rq := by
    change (q : G) ∈ Rq.map Q.subtype ↔ q ∈ Rq
    exact mem_map_iff_mem Q.subtype_injective
  have hCin : ∀ c ∈ C, c ^ 2 = 1 → c ∈ Q := by
    intro c hc hc2
    by_cases hc1 : c = 1
    · exact hc1 ▸ Q.one_mem
    obtain ⟨z, hz, hzQ⟩ := hoverlap
    have hco : orderOf (⟨c, hc⟩ : C) = 2 := by
      rw [← orderOf_coe]
      exact orderOf_eq_prime hc2 hc1
    have heq : c = (z : G) := congrArg (fun c : C => (c : G)) (hunique.unique hco hz)
    exact heq.symm ▸ hzQ
  by_cases hBR : B ≤ R ⊔ C
  · let : IsCyclic R := isCyclic_of_surjective
      (Rq.equivMapOfInjective Q.subtype Q.subtype_injective)
      (Rq.equivMapOfInjective Q.subtype Q.subtype_injective).surjective
    exact card_elementary_le_four_of_cyclic_unique_involution_sup R C B hCtwo hunique
      (hC.trans (centralizer_le hRQ)) hBR
  have hBQ : B ≤ Q := elementary_le_of_involutory_complement Q R C B hC hB hCin
    (fun q hq hout => by
      have hqr : ¬ (⟨q, hq⟩ : Q) ∈ Rq := fun h => hout ((hmem ⟨q, hq⟩).mpr h)
      have hq2 : (⟨q, hq⟩ : Q) ^ 2 = 1 := by
        apply e.injective
        rw [map_pow, map_one]
        cases heq : e ⟨q, hq⟩ with
        | r i => exact (hqr ((hrot _).mpr ⟨i, heq⟩)).elim
        | sr i => simp [pow_two]
      exact congrArg Subtype.val hq2)
    (fun b hb hout q hq hqb => by
      have hbr : ¬ (⟨b, hb⟩ : Q) ∈ Rq := fun h => hout ((hmem ⟨b, hb⟩).mpr h)
      have hqb' : Commute (e ⟨q, hq⟩) (e ⟨b, hb⟩) :=
        (show Commute (⟨q, hq⟩ : Q) ⟨b, hb⟩ from Subtype.ext hqb).map e
      have hq2 : (⟨q, hq⟩ : Q) ^ 2 = 1 := by
        apply e.injective
        rw [map_pow, map_one]
        cases heq : e ⟨b, hb⟩ with
        | r i => exact (hbr ((hrot _).mpr ⟨i, heq⟩)).elim
        | sr i =>
          rw [heq] at hqb'
          exact DihedralGroup.square_eq_one_of_commute_reflection _ i hqb'
      exact congrArg Subtype.val hq2) hBR
  let E := (B.subgroupOf Q).map e.toMonoidHom
  have hE : Nat.card E ≤ 4 := DihedralGroup.card_le_four_of_square_eq_one E (by
    rintro ⟨_, q, hq, rfl⟩
    apply Subtype.ext
    change e q ^ 2 = 1
    rw [← map_pow]
    have hq2 : q ^ 2 = 1 := Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (q : G) hq)
    rw [hq2, map_one])
  rw [card_map_of_injective e.injective,
    Nat.card_congr (subgroupOfEquivOfLe hBQ).toEquiv] at hE
  exact hE

end Subgroup
