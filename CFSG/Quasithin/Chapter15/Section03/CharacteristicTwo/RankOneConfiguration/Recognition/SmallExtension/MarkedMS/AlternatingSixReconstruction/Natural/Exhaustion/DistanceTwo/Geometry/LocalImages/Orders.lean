module
public import Theory.SpecificGroups.Alternating.SixSubgroupObstructions
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Orders of the central critical images in S₆

A nontrivial central subgroup properly contained in a two-subgroup of S₆
has order two or four. An order-eight central subgroup would have cyclic
quotient of order two in a Sylow subgroup of order sixteen, forcing that
Sylow subgroup to be abelian. The explicit noncommuting involutions in A₆
exclude this possibility. No point-radical placement is assumed.

The actual critical-image application, with its quotient map and central
attachment, is in LocalImages.Source. This isolates the order-four case
which must still be excluded for MS93 (3.3)(ii)(2) and (3.6), pp.866--871.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages

private theorem two_subgroup_card_le_sixteen (B : Subgroup (Equiv.Perm (Fin 6)))
    (hp : IsPGroup 2 B) : Nat.card B ≤ 16 := by
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  have hc : Nat.card (P : Subgroup (Equiv.Perm (Fin 6))) = 16 := by
    rw [P.card_eq_multiplicity,Nat.card_perm,Nat.card_fin]
    decide +kernel
  exact (card_le_of_le hP).trans_eq hc

private theorem not_commutative_sixteen (B : Subgroup (Equiv.Perm (Fin 6)))
    (hc : Nat.card B = 16) : ¬ IsMulCommutative B := by
  intro hcomm
  let := hcomm
  let P : Sylow 2 (Equiv.Perm (Fin 6)) := Sylow.ofCard B (by
    rw [hc,Nat.card_perm,Nat.card_fin]
    decide +kernel)
  exact alternatingGroup.SixSubgroupObstructions.not_injective_of_sylow_involutions_commute
    P (by
      change ∀ a b : B, a ^ 2 = 1 → b ^ 2 = 1 → Commute a b
      intro a b _ _
      exact mul_comm a b) (alternatingGroup (Fin 6)).subtype Subtype.coe_injective

/-- A nontrivial central subgroup properly contained in a two-subgroup of S6
has order two or four. The order-eight possibility would make its larger
central extension a commutative Sylow subgroup of order sixteen. -/
theorem central_proper_image_order
    (A B : Subgroup (Equiv.Perm (Fin 6)))
    (hp : IsPGroup 2 B) (hAB : A ≤ B) (hne : A ≠ ⊥)
    (hproper : ¬ B ≤ A) (hc : B ≤ centralizer (A : Set (Equiv.Perm (Fin 6)))) :
    Nat.card A = 2 ∨ Nat.card A = 4 := by
  have hB16 := two_subgroup_card_le_sixteen B hp
  have hlt : Nat.card A < Nat.card B := by
    have hle := card_le_of_le hAB
    have hne : Nat.card A ≠ Nat.card B := by
      intro he
      exact hproper (eq_of_le_of_card_ge hAB he.ge).ge
    omega
  have hpA := hp.of_injective (inclusion hAB) (inclusion_injective hAB)
  obtain ⟨n,hn⟩ := hpA.exists_card_eq
  have hn1 : 1 < Nat.card A := (A.one_lt_card_iff_ne_bot).mpr hne
  have hn4 : n < 4 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    change 2 ^ n < 16
    omega
  have hne8 : Nat.card A ≠ 8 := by
    intro h8
    obtain ⟨m,hm⟩ := hp.exists_card_eq
    have hmle : m ≤ 4 := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      change 2 ^ m ≤ 16
      omega
    have hmgt : 3 < m := by
      apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
      change 8 < 2 ^ m
      omega
    have hm4 : m = 4 := by omega
    have h16 : Nat.card B = 16 := by rw [hm,hm4]; norm_num
    let C := A.subgroupOf B
    have hC : C ≤ center B := by
      intro a ha
      apply mem_center_iff.mpr
      intro b
      exact Subtype.ext (hc b.property a.val ha).symm
    let : C.Normal := normal_subgroupOf_of_le_normalizer
      (hc.trans (centralizer_le_normalizer _))
    have hC8 : Nat.card C = 8 :=
      (Nat.card_congr (subgroupOfEquivOfLe hAB).toEquiv).trans h8
    have hindex : C.index = 2 := by
      have hh := C.card_mul_index
      rw [hC8,h16] at hh
      omega
    let : IsCyclic (B ⧸ C) := isCyclic_of_prime_card (p := 2) hindex
    have hcomm := (QuotientGroup.mk' C).isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [QuotientGroup.ker_mk']; exact hC)
    exact not_commutative_sixteen B h16 hcomm
  have hnCases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hnCases with hn0 | hn1' | hn2 | hn3
  · have hh : Nat.card A = 1 := by simpa [hn0] using hn
    omega
  · exact Or.inl (by simpa [hn1'] using hn)
  · exact Or.inr (by simpa [hn2] using hn)
  · exact (hne8 (by simpa [hn3] using hn)).elim

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
