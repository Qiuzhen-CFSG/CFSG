module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card

/-!
# A Sylow-fixed point in a four-point action

An orbit containing a Sylow-fixed point has odd size. On a four-element
set it has size one or three; in the latter case its singleton complement
is fixed. The action need not be faithful.

Source application: the four cubic subgroups of an elementary nine-group
in Aschbacher--Smith 15.4.9, printed p.1159.
-/

public section
namespace MulAction
variable {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]

/-- A Sylow two-subgroup fixing a point in a four-point action forces a
point fixed by the whole group. The resulting point may be different. -/
theorem exists_fixed_of_card_four_of_sylow_fixed (hX : Nat.card X = 4)
    (S : Sylow 2 G) (x : X) (hx : ∀ g ∈ (S : Subgroup G), g • x = x) :
    ∃ y : X, ∀ g : G, g • y = y := by
  classical
  let O := orbit G x
  have hSO : (S : Subgroup G) ≤ stabilizer G x := hx
  have hindex : (stabilizer G x).index = O.ncard :=
    (Nat.card_congr (orbitEquivQuotientStabilizer G x)).symm
  have hodd : ¬ 2 ∣ O.ncard := by
    rw [← hindex]
    exact fun h => S.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hSO))
  have hpos : 0 < O.ncard := by
    exact (Set.ncard_pos O.toFinite).mpr ⟨x, mem_orbit_self x⟩
  have hbound : O.ncard ≤ 4 := by
    simpa only [Set.ncard_univ, hX] using Set.ncard_le_ncard (Set.subset_univ O)
  have hcases : O.ncard = 1 ∨ O.ncard = 3 := by omega
  rcases hcases with h | h
  · obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp h
    refine ⟨y, fun g => ?_⟩
    have hym : y ∈ O := hy ▸ Set.mem_singleton y
    obtain ⟨a, ha⟩ := hym
    change a • x = y at ha
    have hgm : g • y ∈ O := ⟨g * a, by change (g * a) • x = g • y; rw [mul_smul, ha]⟩
    simpa only [hy, Set.mem_singleton_iff] using hgm
  · have hcomp : Oᶜ.ncard = 1 := by
      have hh := Set.ncard_add_ncard_compl O
      rw [h, hX] at hh
      omega
    obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp hcomp
    refine ⟨y, fun g => ?_⟩
    have hym : y ∈ Oᶜ := hy ▸ Set.mem_singleton y
    have hgm : g • y ∈ Oᶜ := by
      intro hg
      obtain ⟨a, ha⟩ := hg
      change a • x = g • y at ha
      apply hym
      exact ⟨g⁻¹ * a, by change (g⁻¹ * a) • x = y; rw [mul_smul, ha, inv_smul_smul]⟩
    simpa only [hy, Set.mem_singleton_iff] using hgm

end MulAction
