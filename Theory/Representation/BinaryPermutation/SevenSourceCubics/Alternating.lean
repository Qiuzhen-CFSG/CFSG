module
public import Theory.Representation.BinaryPermutation.SevenSourceCubics
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.Quasithin.Rank

/-!
# The source weight-four cubics inside A₇

Intersecting the marked Sylow and its local overgroups with A₇ gives
orders eight and twenty-four. Each of the two even cubics retains the
literal S₃-over-Sylow quotient. Both fix the weight-four point and their
join has three-rank two, as required for the full-kernel application.
Source: Aschbacher–Smith 14.7.50, printed p.1065, refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Equiv Representation Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
namespace BinaryPermutation.SevenSourceCubics.Alternating
abbrev A7 := alternatingGroup (Fin 7)
def two : Subgroup A7 := standardTwo.subgroupOf A7
instance (a : A7) : Decidable (a ∈ two) :=
  inferInstanceAs (Decidable (a.val ∈ standardTwo))
def first : A7 := ⟨SevenSourceCubics.first, by rw [Perm.mem_alternatingGroup]; decide⟩
def second : A7 := ⟨SevenSourceCubics.second, by rw [Perm.mem_alternatingGroup]; decide⟩
def firstGroup : Subgroup A7 := zpowers first
def secondGroup : Subgroup A7 := zpowers second

private theorem even_card (P : Subgroup S7) (t : S7) (ht : t ∈ P)
    (ho : t ∉ alternatingGroup (Fin 7)) :
    Nat.card (P.subgroupOf A7) * 2 = Nat.card P := by
  have hd := (alternatingGroup (Fin 7)).relIndex_dvd_index_of_normal P
  rw [alternatingGroup.index_eq_two] at hd
  have hi : (alternatingGroup (Fin 7)).relIndex P = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
      (fun hh => ho ((relIndex_eq_one.mp hh) ht))
  let e : (A7.subgroupOf P) ≃ (P.subgroupOf A7) := {
    toFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
    invFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hh := (A7.subgroupOf P).card_mul_index
  change Nat.card (A7.subgroupOf P) * A7.relIndex P = Nat.card P at hh
  rwa [Nat.card_congr e,hi] at hh

theorem two_card : Nat.card two = 8 := by
  have hh := even_card standardTwo (swap 0 1) (by decide) (by rw [Perm.mem_alternatingGroup]; decide)
  rw [standardTwo_card] at hh
  change Nat.card two * 2 = 16 at hh
  omega

noncomputable def sylow : Sylow 2 A7 :=
  (standardSylow.isPGroup'.comap_subtype : IsPGroup 2 two).toSylow (by
    have hh := two.card_mul_index
    rw [two_card,nat_card_alternatingGroup,Nat.card_fin] at hh
    norm_num at hh
    have hi : two.index = 315 := by omega
    change ¬ 2 ∣ two.index
    rw [hi]
    decide)

theorem first_order : orderOf first = 3 :=
  orderOf_eq_prime (by decide : first ^ 3 = 1) (by decide)
theorem second_order : orderOf second = 3 :=
  orderOf_eq_prime (by decide : second ^ 3 = 1) (by decide)
theorem first_card : Nat.card firstGroup = 3 := (Nat.card_zpowers first).trans first_order
theorem second_card : Nat.card secondGroup = 3 := (Nat.card_zpowers second).trans second_order

theorem cubic_join_quotient (r : A7) (hr : orderOf r = 3)
    (P : Subgroup S7) (hSP : standardTwo ≤ P) (hrP : r.val ∈ P)
    (hP : Nat.card P = 48) (t : A7) (ht : t ∈ two)
    (hnt : r * t * r⁻¹ ∉ two) :
    Nonempty (((zpowers r ⊔ two : Subgroup A7) ⧸
      pCore 2 (zpowers r ⊔ two : Subgroup A7)) ≃* Perm (Fin 3)) := by
  let J := zpowers r ⊔ two
  have hJP : J ≤ P.subgroupOf A7 := sup_le (zpowers_le.mpr hrP) (fun x hx => hSP hx)
  have hSJ : two ≤ J := le_sup_right
  have h3 : 3 ∣ Nat.card J := by
    have hh := card_dvd_of_le (show zpowers r ≤ J from le_sup_left)
    rwa [Nat.card_zpowers,hr] at hh
  have h8 : 8 ∣ Nat.card J := two_card ▸ card_dvd_of_le hSJ
  have hd : 24 ∣ Nat.card J :=
    (show Nat.Coprime 3 8 by decide).mul_dvd_of_dvd_of_dvd h3 h8
  have hhalf : Nat.card (P.subgroupOf A7) = 24 := by
    have hh := even_card P (swap 0 1) (hSP (by decide)) (by rw [Perm.mem_alternatingGroup]; decide)
    rw [hP] at hh
    omega
  have hj : Nat.card J = 24 := le_antisymm
    (hhalf ▸ card_le_of_le hJP) (Nat.le_of_dvd Nat.card_pos hd)
  let S := sylow.subtype hSJ
  have hs : Nat.card S = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hSJ).toEquiv).trans two_card
  have hi : (S : Subgroup J).index = 3 := by
    have hh := (S : Subgroup J).card_mul_index
    rw [hs,hj] at hh
    omega
  apply sylow_index_three_core_quotient S hi
  apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal S)
  intro he
  have hn : (S : Subgroup J).Normal := he ▸ inferInstance
  have hnorm : J ≤ normalizer (two : Set A7) :=
    (normal_subgroupOf_iff_le_normalizer hSJ).mp hn
  exact hnt ((mem_normalizer_iff.mp (hnorm
    ((show zpowers r ≤ J from le_sup_left) (mem_zpowers r))) t).mp ht)

/-- Both even cubics have S₃ joins with the actual alternating Sylow. -/
theorem first_join_quotient :
    Nonempty (((firstGroup ⊔ two : Subgroup A7) ⧸
      pCore 2 (firstGroup ⊔ two : Subgroup A7)) ≃* Perm (Fin 3)) :=
  cubic_join_quotient first first_order cubicOvergroup standardTwo_le_cubic (by decide)
    cubicOvergroup_card ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩ (by decide) (by decide)
theorem second_join_quotient :
    Nonempty (((secondGroup ⊔ two : Subgroup A7) ⧸
      pCore 2 (secondGroup ⊔ two : Subgroup A7)) ≃* Perm (Fin 3)) :=
  cubic_join_quotient second second_order duadOvergroup inf_le_left (by decide)
    duadOvergroup_card ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩ (by decide) (by decide)

/-- The same order-nine subgroup lies in A₇, with both cubic axes retained. -/
theorem two_le_join_rank : 2 ≤ primeRank 3 (firstGroup ⊔ secondGroup : Subgroup A7) := by
  have hm : (firstGroup ⊔ secondGroup).map A7.subtype =
      SevenSourceCubics.firstGroup ⊔ SevenSourceCubics.secondGroup := by
    rw [Subgroup.map_sup,firstGroup,secondGroup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    rfl
  rw [primeRank_congr 3 (equivMapOfInjective (firstGroup ⊔ secondGroup)
    A7.subtype A7.subtype_injective),hm]
  exact SevenSourceCubics.two_le_join_rank

theorem firstGroup_fixes : ∀ a ∈ firstGroup,
    alternatingCoreRepresentation (Fin 7) a point = point := by
  intro a ha
  apply SevenSourceCubics.firstGroup_fixes a.val
  have hh := mem_map_of_mem A7.subtype ha
  simpa only [firstGroup,MonoidHom.map_zpowers,first,SevenSourceCubics.firstGroup,Subgroup.coe_subtype] using hh

theorem secondGroup_fixes : ∀ a ∈ secondGroup,
    alternatingCoreRepresentation (Fin 7) a point = point := by
  intro a ha
  apply SevenSourceCubics.secondGroup_fixes a.val
  have hh := mem_map_of_mem A7.subtype ha
  simpa only [secondGroup,MonoidHom.map_zpowers,second,SevenSourceCubics.secondGroup,Subgroup.coe_subtype] using hh
end BinaryPermutation.SevenSourceCubics.Alternating
