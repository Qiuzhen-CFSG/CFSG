module
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupAction.SmallQuotientCentralization
public import Theory.GroupTheory.Commutator.CoprimeQuadratic
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Sylow normalizers with a central omega quotient of order at most two

The normalizer of a Sylow two-subgroup centralizes its omega-center when
that omega-center modulo the ambient center has order at most two.
Schur–Zassenhaus splits the normalizer over the Sylow subgroup. Its odd
complement acts quadratically on the omega-center, and coprime quadratic
actions are trivial; the Sylow factor already centralizes its own center.

This is the elementary normalizer step for the A₅-block Borel in
Aschbacher–Smith C.1.29, printed p.134, and E.6.7, printed p.246.
-/

public section
open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G]

theorem normalizer_centralizes_omegaCenter_of_small_quotient (P : Sylow 2 G)
    (hcard : Nat.card (omegaCenterIn (P : Subgroup G) ⧸
      (center G).subgroupOf (omegaCenterIn (P : Subgroup G))) ≤ 2) :
    normalizer (P : Set G) ≤ centralizer (omegaCenterIn (P : Subgroup G) : Set G) := by
  let A := normalizer (P : Set G)
  let U := omegaCenterIn (P : Subgroup G)
  let PN : Sylow 2 A := P.subtype (P : Subgroup G).le_normalizer
  let : (PN : Subgroup A).Normal := Subgroup.normal_in_normalizer
  obtain ⟨T,hT⟩ := exists_right_complement'_of_coprime PN.card_coprime_index
  let R := T.map A.subtype
  have hRA : R ≤ A := map_subtype_le _
  have hodd : Odd (Nat.card R) := by
    rw [card_map_of_injective A.subtype_injective, ←hT.symm.index_eq_card]
    simpa only [←even_iff_two_dvd, Nat.not_even_iff_odd] using PN.not_dvd_index
  have hgen : A = (P : Subgroup G) ⊔ R := by
    have hh := congrArg (Subgroup.map A.subtype) hT.sup_eq_top
    rw [Subgroup.map_sup, show (PN : Subgroup A) = (P : Subgroup G).subgroupOf A from rfl, map_subgroupOf_eq_of_le (show (P : Subgroup G) ≤ A from (P : Subgroup G).le_normalizer),
      ←MonoidHom.range_eq_map, range_subtype] at hh
    exact hh.symm
  have hAU : A ≤ normalizer (U : Set G) := normalizer_le_normalizer_omegaCenterIn _
  have hsmall : ⁅U,R⁆ ≤ center G :=
    commutator_le_of_normalized_quotient_card_le_two R U (center G)
      (hRA.trans hAU) (by rw [normalizer_eq_top]; exact le_top) inferInstance hcard
  have hc : ⁅U,R⁆ = ⊥ := by
    apply commutator_eq_bot_of_coprime_quadratic U R (hRA.trans hAU)
      (Group.isSolvable_of_comm (fun a b : U => mul_comm' a b)) ?_ ?_
    · obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_card_eq
      rw [hn]
      exact hodd.coprime_two_right.pow_right n
    · apply bot_unique
      exact (commutator_mono hsmall le_rfl).trans (commutator_center_left R).le
  change A ≤ centralizer (U : Set G)
  rw [hgen]
  apply sup_le
  · apply le_centralizer_iff.mp
    intro u hu
    exact (mem_omegaCenterIn_iff _ _).mp hu |>.2.1
  · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))

end Sylow
