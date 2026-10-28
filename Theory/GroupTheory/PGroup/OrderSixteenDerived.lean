module

public import Theory.GroupTheory.PGroup.SmallOrderDerived
public import Theory.GroupTheory.PGroup.CyclicAbelianization
public import Theory.GroupTheory.NormalFourCentralizer

/-!
# Cyclic derived subgroups in two-groups of order at most sixteen

A noncyclic derived subgroup would be an elementary four. Its centralizer
has index at most two. If proper, this centralizer has order at most eight
and center of order at least four, so is abelian. In an abelian index-two
extension with elementary derived subgroup, every square is central. The
derived four is consequently central, and the central quotient has order
at most four, contradicting the two-generator commutator calculation.

This intrinsic argument uses no classification of groups of order sixteen.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace IsPGroup
variable {P : Type*} [Group P] [Finite P]

omit [Finite P] in
private theorem squares_central_of_abelian_index_two
    (C : Subgroup P) [IsMulCommutative C] (hi : C.index = 2)
    (hcomm : ∀ x y : P, ⁅x,y⁆ ^ 2 = 1) :
    ∀ x : P, x ^ 2 ∈ center P := by
  let : C.Normal := C.normal_of_index_eq_two hi
  intro x
  apply mem_center_iff.mpr
  intro y
  by_cases hx : x ∈ C
  · by_cases hy : y ∈ C
    · exact C.le_centralizer (C.pow_mem hx 2) y hy
    · have ha : y*x*y⁻¹ ∈ C := Subgroup.Normal.conj_mem inferInstance x hx y
      have hc : Commute (y*x*y⁻¹) x⁻¹ :=
        C.le_centralizer (C.inv_mem hx) _ ha
      have hh := hcomm y x
      change ((y*x*y⁻¹)*x⁻¹)^2 = 1 at hh
      rw [hc.mul_pow,inv_pow,mul_inv_eq_one] at hh
      have he : y*x^2*y⁻¹ = x^2 := by
        calc
          y*x^2*y⁻¹ = (y*x*y⁻¹)^2 := by simp only [pow_two]; group
          _ = x^2 := hh
      exact mul_inv_eq_iff_eq_mul.mp he
  · have hx2 := C.sq_mem_of_index_two hi x
    by_cases hy : y ∈ C
    · exact C.le_centralizer hx2 y hy
    · have ha : y*x⁻¹ ∈ C :=
        (C.mul_mem_iff_of_index_two hi).mpr (by simpa using iff_of_false hy hx)
      have hc : Commute (y*x⁻¹) (x^2) := C.le_centralizer hx2 _ ha
      have hh := hc.mul_left (Commute.self_pow x 2)
      simpa only [inv_mul_cancel_right] using hh.eq

/-- Every finite two-group of order at most sixteen has cyclic derived subgroup. -/
theorem isCyclic_commutator_of_card_le_sixteen (hP : IsPGroup 2 P)
    (hcard : Nat.card P ≤ 16) : IsCyclic (commutator P) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hn
  have hnonab : ¬ IsMulCommutative P := by
    intro ha
    apply hn
    rw [(commutator_eq_bot_iff P).mpr ha]
    infer_instance
  have hiD : 4 ≤ Nat.card (P ⧸ commutator P) := by
    obtain ⟨n,he⟩ := (hP.to_quotient (commutator P)).exists_card_eq
    have hn2 : 2 ≤ n := by
      by_contra! hlt
      let : IsCyclic (P ⧸ commutator P) := isCyclic_of_card_dvd_prime (p := 2) (by
        rw [he]
        interval_cases n <;> norm_num)
      let : IsCyclic P := hP.isCyclic_of_cyclic_abelianization
      exact hnonab inferInstance
    rw [he]
    exact Nat.pow_le_pow_right (n := 2) (by decide) hn2
  have hDle : Nat.card (commutator P) ≤ 4 := by
    have hh := (commutator P).card_mul_index
    change Nat.card (commutator P) * Nat.card (P ⧸ commutator P) = Nat.card P at hh
    nlinarith
  have hD : Nat.card (commutator P) = 4 := by
    obtain ⟨n,he⟩ := (hP.to_subgroup (commutator P)).exists_card_eq
    have hn2 : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by
      simpa only [←he] using hDle)
    interval_cases n
    · exact (hn (isCyclic_of_card_dvd_prime (p := 2) (by rw [he]; norm_num))).elim
    · exact (hn (isCyclic_of_card_dvd_prime (p := 2) (by rw [he]; norm_num))).elim
    · exact he
  let : IsMulCommutative (commutator P) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hD
  let : IsElementaryAbelian 2 (commutator P) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      have hd : orderOf x ∣ 2^2 := by simpa [hD] using orderOf_dvd_natCard x
      obtain ⟨n,hn2,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      have hne : orderOf x ≠ 4 := fun hx => hn (isCyclic_of_orderOf_eq_card x (hx.trans hD.symm))
      have hdiv : orderOf x ∣ 2 := by
        interval_cases n
        · rw [he]; norm_num
        · rw [he]; norm_num
        · exact (hne he).elim
      exact orderOf_dvd_iff_pow_eq_one.mp hdiv) }
  have finish (hcentral : commutator P ≤ center P) : False := by
    have hZ : 4 ≤ Nat.card (center P) := hD ▸ card_le_of_le hcentral
    have hquot : Nat.card (P ⧸ center P) ≤ 4 := by
      have hh := (center P).card_mul_index
      change Nat.card (center P) * Nat.card (P ⧸ center P) = Nat.card P at hh
      nlinarith
    exact hn (hP.isCyclic_commutator_of_card_center_quotient_le_four hquot)
  let C := centralizer (commutator P : Set P)
  have hi : C.index ≤ 2 := centralizer_index_le_two_of_normal_four hP _ hD
  by_cases htop : C = ⊤
  · exact finish (centralizer_eq_top_iff_subset.mp htop)
  have hi2 : C.index = 2 := by
    have hh := C.one_lt_index_of_ne_top htop
    omega
  have hC : Nat.card C ≤ 8 := by
    have hh := C.card_mul_index
    rw [hi2] at hh
    omega
  have hDC : commutator P ≤ C := (commutator P).le_centralizer
  have hDZ : (commutator P).subgroupOf C ≤ center C := by
    intro d hd
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (c.property d hd).symm
  have hZC : 4 ≤ Nat.card (center C) := by
    have hh := card_le_of_le hDZ
    rwa [Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv,hD] at hh
  have hCquot : Nat.card (C ⧸ center C) ≤ 2 := by
    have hh := (center C).card_mul_index
    change Nat.card (center C) * Nat.card (C ⧸ center C) = Nat.card C at hh
    nlinarith
  have hCdiv : Nat.card (C ⧸ center C) ∣ 2 := by
    obtain ⟨n,he⟩ := ((hP.to_subgroup C).to_quotient (center C)).exists_card_eq
    have hn1 : n ≤ 1 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by
      simpa only [←he] using hCquot)
    rw [he]
    exact pow_dvd_pow 2 hn1
  let : IsCyclic (C ⧸ center C) := isCyclic_of_card_dvd_prime (p := 2) hCdiv
  let : IsMulCommutative C := isMulCommutative_of_isCyclic_quotient_center_self C
  have hsquares := squares_central_of_abelian_index_two C hi2 (fun x y =>
    elemPow_eq_one_of_isElementaryAbelian (A := commutator P) _
      (commutator_mem_commutator (mem_top x) (mem_top y)))
  have hab : IsMulCommutative (P ⧸ center P) := ⟨⟨fun x y =>
    (Commute.of_orderOf_dvd_two (fun z => by
      obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (center P) z
      apply orderOf_dvd_iff_pow_eq_one.mpr
      rw [←map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hsquares z)) x y).eq⟩⟩
  exact finish (Normal.quotient_commutative_iff_commutator_le.mp hab)

end IsPGroup
