module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.Structure
public import Theory.GroupTheory.PerfectCentralCoverRank
public import Theory.GroupTheory.PrimeRankZero

/-!
# Uniqueness of the lifted component

A second component commutes with the chosen high-three-rank component. The
ambient rank bound puts all its cubic elements in the chosen component's
center. If that center has order at most three, every elementary subgroup
of the second component has order at most three, so its Sylow three-groups
are cyclic. Transfer in a perfect group then kills its central cubic
elements. Thus any second component has order prime to three. The B.5.5
application excludes exactly that remaining possibility in the selected cover.

Source: the component-uniqueness step of Aschbacher–Smith B.5.7, p.105;
the cyclic Sylow transfer argument is I.1.2, p.407.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction
variable {H : Type*} [Group H] [Finite H]

/-- A distinct commuting component cannot have positive three-rank. -/
theorem other_component_rank_zero {M D : Subgroup H}
    (hM : IsComponent H M) (hD : IsComponent H D) (hne : D ≠ M)
    (hrM : 1 < primeRank 3 M) (hrH : primeRank 3 H ≤ 2)
    (hz : Nat.card (center M) ≤ 3) : primeRank 3 D = 0 := by
  let := hD.2
  have hc : D ≤ centralizer (M : Set H) :=
    commutator_eq_bot_iff_le_centralizer.mp (hD.commutator_eq_bot_of_ne hM hne)
  have hcube (x : D) (hx : x ^ 3 = 1) : (x : H) ∈ (center M).map M.subtype :=
    centralizer_cube_mem_center M hrM hrH x (hc x.property)
      (congrArg D.subtype hx)
  have hsmall (E : Subgroup D) (he : IsElementaryAbelian 3 E) : Nat.card E ≤ 3 := by
    let := he
    have hle : E.map D.subtype ≤ (center M).map M.subtype := by
      rintro _ ⟨x, hx, rfl⟩
      apply hcube
      exact congrArg E.subtype (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 E) ⟨x, hx⟩)
    have hcard := card_le_of_le hle
    rw [card_map_of_injective D.subtype_injective,
      card_map_of_injective M.subtype_injective] at hcard
    exact hcard.trans hz
  apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := D) 3 hd
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hxM : (x : H) ∈ M := (map_subtype_le _) (hcube x hx3)
  have hxZ : x ∈ center D := by
    apply mem_center_iff.mpr
    intro d
    exact Subtype.ext ((mem_centralizer_iff.mp (hc d.property)) x hxM).symm
  have hp : IsPGroup 3 (zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    simp [Nat.card_zpowers, hx]
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  let xP : P := ⟨x, hP (mem_zpowers x)⟩
  have hxPc : (zpowers xP).map (P : Subgroup D).subtype ≤ center D := by
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr hxZ
  have hbot := PerfectCentralCovering.central_subgroup_eq_bot_of_isCyclic_sylow P
    (P.isCyclic_of_odd_of_elementary_card_le (by decide) hsmall) (zpowers xP) hxPc
  have hxP1 : xP = 1 := by
    have he := mem_zpowers xP
    rwa [hbot, mem_bot] at he
  have hx1 : x = 1 := congrArg (P : Subgroup D).subtype hxP1
  simp [hx1] at hx

/-- Positive three-rank for every component now proves the entire layer equality. -/
theorem layer_eq_of_components_positive {M : Subgroup H}
    (hM : IsComponent H M) (hrM : 1 < primeRank 3 M)
    (hrH : primeRank 3 H ≤ 2) (hz : Nat.card (center M) ≤ 3)
    (hpos : ∀ D : Subgroup H, IsComponent H D → 0 < primeRank 3 D) :
    componentLayer H = M := by
  apply le_antisymm
  · apply sSup_le
    intro D hD
    by_cases he : D = M
    · exact he.le
    · exact (Nat.ne_of_gt (hpos D hD)
        (other_component_rank_zero hM hD he hrM hrH hz)).elim
  · exact le_sSup hM

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction
