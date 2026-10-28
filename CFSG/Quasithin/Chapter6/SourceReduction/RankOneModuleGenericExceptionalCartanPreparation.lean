module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericCartan
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction

/-!
# Choosing the two compatible Cartans in the generic rank-one argument

The solvable intersection M ∩ H normalizes the solvable local Borel
N_L(T ∩ L). Choose an odd Hall subgroup B of M ∩ H, then extend B to an
odd Hall subgroup E of their product. The intersection of E with the local
Borel is an odd Hall subgroup A normalized by B. Both Hall conditions use
their original ambient subgroups; neither is replaced by odd order alone.

This proves the Hall-theoretic step of 5.1.5(2) and Notation 5.1.9. The
preceding solvability and normalization assertions remain explicit inputs.
The Chapter 12 application is in RankOneModuleGenericExceptionalCartan.
Source: Aschbacher--Smith, printed pp.631,634.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The precise earlier geometric facts needed for the compatible Hall
construction. These are assertions of 5.1.5, not an exceptional conclusion. -/
structure CartanPreparation (T : Sylow 2 G) (L H : Subgroup G) : Prop where
  borel_solvable : Group.IsSolvable (localBorel T L)
  intersection_solvable : Group.IsSolvable (normalizer (L : Set G) ⊓ H : Subgroup G)
  intersection_normalizes : normalizer (L : Set G) ⊓ H ≤
    normalizer (localBorel T L : Set G)

/-- Hall existence in the normalized product supplies the compatible pair
without making either Hall subgroup a premise. -/
theorem CartanPreparation.exists_cartanPair {T : Sylow 2 G} {L H : Subgroup G}
    (h : CartanPreparation T L H) :
    ∃ A B : Subgroup G, CartanPair T L H A B := by
  let C := localBorel T L
  let M := normalizer (L : Set G) ⊓ H
  let J := C ⊔ M
  let : Group.IsSolvable C := h.borel_solvable
  let : Group.IsSolvable M := h.intersection_solvable
  have hJ : Group.IsSolvable J :=
    Group.isSolvable_sup_of_normalizes C M h.intersection_normalizes
  obtain ⟨B, _, hBM, hB⟩ := OddHall.exists_hall_containing_odd M ⊥
    h.intersection_solvable bot_le (by simp)
  have hBo : Odd (Nat.card B) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro hb
    apply hB.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ _ rfl
    rwa [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv]
  obtain ⟨E, hBE, hEJ, hE⟩ := OddHall.exists_hall_containing_odd J B hJ
    (hBM.trans le_sup_right) hBo
  have hJN : J ≤ normalizer (C : Set G) :=
    sup_le C.le_normalizer h.intersection_normalizes
  have hA := OddHall.hall_restrict_of_normalizes hE hEJ
    (show C ≤ J from le_sup_left) (hEJ.trans hJN)
  refine ⟨E ⊓ C, B, inf_le_right, ?_, hBM, hB, ?_⟩
  · change IsHallSubgroup OddHall.oddPrimes ((E ⊓ C).subgroupOf C)
    rwa [inf_subgroupOf_right]
  · intro b hb
    apply mem_normalizer_iff.mpr
    intro x
    change (x ∈ E ∧ x ∈ C) ↔ b * x * b⁻¹ ∈ E ∧ b * x * b⁻¹ ∈ C
    exact and_congr ((mem_normalizer_iff.mp (E.le_normalizer (hBE hb))) x)
      ((mem_normalizer_iff.mp (h.intersection_normalizes (hBM hb))) x)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
