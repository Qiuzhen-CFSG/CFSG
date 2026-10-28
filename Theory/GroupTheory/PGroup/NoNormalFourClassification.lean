module

public import Theory.GroupTheory.PGroup.NoNormalFourIndex
public import Theory.GroupTheory.InvolutionCentralizerFourRecognition

/-!
# Recognizing two-groups without normal four-groups

Every finite two-group without normal elementary four-groups has a cyclic
normal self-centralizing subgroup of index at most two. If the group contains
an elementary four-group, that cyclic subgroup is proper and has index two.
For a cyclic normal self-centralizing subgroup of index two, the absence of
normal elementary four-groups forces every involution outside that subgroup
to have centralizer of order four. An elementary four-group supplies such an
involution. The involution-centralizer recognition theorem then gives a
dihedral isomorphism or an explicit semidihedral presentation.

The fixed subgroup in the cyclic subgroup has order at most two by the
involution-action calculation, while adjoining the outer involution gives
a subgroup of order four. This is the recognition step for GLS, Number 2,
Chapter C, Lemma 10.11.
-/

open Subgroup

namespace IsPGroup

/-- An involution outside a cyclic normal self-centralizing subgroup of index
two has centralizer of order four if the group has no normal four-group. -/
public theorem centralizer_card_four_of_no_normal_four_of_cyclic_index_two
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4)
    (A : Subgroup P) [A.Normal] [IsCyclic A]
    (hC : centralizer (A : Set P) ≤ A) (hindex : A.index = 2)
    (e : P) (he : e ^ 2 = 1) (heA : e ∉ A) :
    Nat.card (centralizer ({e} : Set P)) = 4 := by
  let C := centralizer ({e} : Set P)
  let I := C ⊓ A
  let : IsCyclic I := Subgroup.isCyclic_of_le (show I ≤ A from inf_le_right)
  have hIc : Nat.card I ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    apply Subtype.ext
    exact hP.fixed_sq_eq_one_of_no_normal_four hno A hC e he heA x x.property.2
      (mem_centralizer_singleton_iff.mp x.property.1)
  have hIle : Nat.card I ≤ 2 := Nat.le_of_dvd (by decide) hIc
  have hidx : I.relIndex C ∣ 2 := by
    change (C ⊓ A).relIndex C ∣ 2
    rw [inf_relIndex_left]
    exact hindex ▸ A.relIndex_dvd_index_of_normal C
  have hidxle : I.relIndex C ≤ 2 := Nat.le_of_dvd (by decide) hidx
  have hm := (I.subgroupOf C).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show I ≤ C from inf_le_left)).toEquiv] at hm
  change Nat.card I * I.relIndex C = Nat.card C at hm
  have hupper : Nat.card C ≤ 4 := by nlinarith
  have hAtwo : 2 ∣ Nat.card A := by
    rcases (hP.to_subgroup A).card_eq_or_dvd with h | h
    · have hAbot : A = ⊥ := card_eq_one.mp h
      have heC : e ∈ centralizer (A : Set P) := by
        rw [hAbot]
        intro x hx
        have hx1 : x = 1 := by simpa using hx
        simp [hx1]
      exact (heA (hC heC)).elim
    · exact h
  obtain ⟨zA, hzA⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 hAtwo
  let z : P := zA
  have hz : orderOf z = 2 := by simpa [z] using hzA
  have hzC : z ∈ C := by
    have hezA : e * z * e⁻¹ ∈ A := Normal.conj_mem inferInstance z zA.property e
    have hez : orderOf (e * z * e⁻¹) = 2 := by
      rw [← MulAut.conj_apply, (MulAut.conj e).orderOf_eq, hz]
    have heq : e * z * e⁻¹ = z := congrArg Subtype.val
      (IsCyclic.eq_of_orderOf_eq_two
        (x := (⟨e * z * e⁻¹, hezA⟩ : A)) (y := zA)
        (by simpa using hez) hzA)
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp heq).symm
  have heC : e ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have heout : e ∉ zpowers z := fun hh => heA (zpowers_le.mpr zA.property hh)
  have henorm : e ∈ normalizer (zpowers z : Set P) := by
    apply centralizer_le_normalizer
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    exact ((show Commute z e from mem_centralizer_singleton_iff.mp hzC).zpow_left k).eq
  have hfour : Nat.card (zpowers z ⊔ zpowers e : Subgroup P) = 4 := by
    rw [card_sup_zpowers_of_normalizing_involution (zpowers z) e he heout henorm,
      Nat.card_zpowers, hz]
  have hlower : 4 ≤ Nat.card C := by
    rw [← hfour]
    exact card_le_of_le (sup_le (zpowers_le.mpr hzC) (zpowers_le.mpr heC))
  exact Nat.le_antisymm hupper hlower

/-- Recognition from a cyclic normal self-centralizing subgroup of index two.
The elementary four-group supplies an involution outside the cyclic subgroup. -/
public theorem exists_dihedral_or_semidihedral_of_no_normal_four_of_cyclic_index_two
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4)
    (A : Subgroup P) [A.Normal] [IsCyclic A]
    (hC : centralizer (A : Set P) ≤ A) (hindex : A.index = 2)
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    (∃ m : ℕ, Nonempty (P ≃* DihedralGroup m)) ∨
      (∃ n : ℕ, 4 ≤ n ∧ Nat.card P = 2 ^ n ∧
        ∃ a b : P, orderOf a = 2 ^ (n - 1) ∧ orderOf b = 2 ∧
          b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧
          Subgroup.closure ({a, b} : Set P) = ⊤) := by
  have hEA : ¬ E ≤ A := by
    intro hEA
    let : IsCyclic E := Subgroup.isCyclic_of_le hEA
    have hcard : Nat.card E ∣ 2 := by
      rw [← IsCyclic.exponent_eq_card]
      exact IsElementaryAbelian.exponent_dvd_p 2 E
    norm_num [hE] at hcard
  obtain ⟨e, heE, heA⟩ := SetLike.not_le_iff_exists.mp hEA
  have he : e ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian e heE
  have heorder : orderOf e = 2 := orderOf_eq_prime he (fun h => heA (h ▸ A.one_mem))
  have heZ : e ∉ center P := by
    intro heZ
    exact heA (hC (by intro a _; exact (mem_center_iff.mp heZ a)))
  exact exists_dihedral_or_semidihedral_of_involution_centralizer_card_four hP e heorder heZ
    (hP.centralizer_card_four_of_no_normal_four_of_cyclic_index_two hno A hC hindex e he heA)

/-- A finite two-group containing an elementary four-group but no normal
elementary four-group is dihedral or semidihedral (GLS2, Chapter C,
Lemma 10.11, with the normal subgroup equal to the ambient group). -/
public theorem exists_dihedral_or_semidihedral_of_no_normal_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4)
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    (∃ m : ℕ, Nonempty (P ≃* DihedralGroup m)) ∨
      (∃ n : ℕ, 4 ≤ n ∧ Nat.card P = 2 ^ n ∧
        ∃ a b : P, orderOf a = 2 ^ (n - 1) ∧ orderOf b = 2 ∧
          b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧
          Subgroup.closure ({a, b} : Set P) = ⊤) := by
  obtain ⟨A, hAn, hAc, hC⟩ :=
    hP.exists_cyclic_normal_selfCentralizing_of_no_normal_four hno
  let : A.Normal := hAn
  let : IsCyclic A := hAc
  have hproper : A ≠ ⊤ := by
    intro htop
    let : IsCyclic E := Subgroup.isCyclic_of_le (show E ≤ A by simp [htop])
    have hcard : Nat.card E ∣ 2 := by
      rw [← IsCyclic.exponent_eq_card]
      exact IsElementaryAbelian.exponent_dvd_p 2 E
    norm_num [hE] at hcard
  have hindex : A.index = 2 := by
    have hlower := A.one_lt_index_of_ne_top hproper
    have hupper :=
      hP.index_le_two_of_cyclic_normal_selfCentralizing_of_no_normal_four hno A hC.le
    omega
  exact hP.exists_dihedral_or_semidihedral_of_no_normal_four_of_cyclic_index_two
    hno A hC.le hindex E hE

end IsPGroup
