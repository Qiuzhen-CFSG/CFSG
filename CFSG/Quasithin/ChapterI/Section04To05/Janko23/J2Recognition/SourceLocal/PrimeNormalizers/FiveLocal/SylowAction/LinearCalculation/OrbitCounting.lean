module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction.Reduction
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card

/-!
# The two marked orbits in the five-plane

The four-group has exactly one fixed point on the marked A-orbit: its
other fixed line is excluded by nonfusion. The two-group fixed-point
congruence makes that orbit odd. Together with the line-stabilizer order
bound, this excludes an actor of order 32. For an actor of order 12,
orbit--stabilizer makes both marked orbits have size three; disjointness
then gives coverage of all six lines.

These are the action-theoretic steps in the final paragraph of Aschbacher,
*Sporadic Groups* (1994), 47.2, printed p.261. The plane's line count and
stabilizer bound remain explicit, as does the separate dihedral recognition.
The fixed-line equivalence is applied with an explicit proof that the
subgroup has order five.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction
variable {E : Type*} [Group E] {H : Subgroup (MulAut E)}

theorem inLineOrbit_iff_mem_orbit (A B : Subgroup E) :
    InLineOrbit H A B ↔ B ∈ MulAction.orbit H A := Iff.rfl

private theorem orbit_card_eq {A L : Subgroup E} (h : L ∈ MulAction.orbit H A) :
    Nat.card L = Nat.card A := by
  obtain ⟨g, rfl⟩ := h
  exact Subgroup.card_map_of_injective g.val.injective

private theorem orbit_stabilizer_card (A : Subgroup E) :
    Nat.card (MulAction.orbit H A) * Nat.card (MulAction.stabilizer H A) = Nat.card H := by
  rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H A)]

private theorem fixed_iff_on_lines (F : FourLineFrame H) (L : Subgroup E)
    (hL : Nat.card L = 5) :
    (∀ v : F.four, L.map v.val.val.toMonoidHom = L) ↔ L = F.A ∨ L = F.B :=
  F.fixed L hL

private theorem fixed_A (F : FourLineFrame H) (v : F.four) :
    v.val • F.A = F.A := (fixed_iff_on_lines F F.A F.A_card).mpr (Or.inl rfl) v

private theorem fixed_B (F : FourLineFrame H) (v : F.four) :
    v.val • F.B = F.B := (fixed_iff_on_lines F F.B F.B_card).mpr (Or.inr rfl) v

/-- Nonfusion leaves exactly one four-group fixed point in the actual A-orbit. -/
theorem FourLineFrame.fixedPoints_A_orbit_card (F : FourLineFrame H) :
    Nat.card (MulAction.fixedPoints F.four (MulAction.orbit H F.A)) = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  let a : MulAction.orbit H F.A := ⟨F.A, MulAction.mem_orbit_self F.A⟩
  have ha : a ∈ MulAction.fixedPoints F.four (MulAction.orbit H F.A) := by
    intro v
    exact Subtype.ext (fixed_A F v)
  refine ⟨⟨a, ha⟩, ?_⟩
  intro y
  apply Subtype.ext
  apply Subtype.ext
  have hycard : Nat.card y.val.val = 5 := (orbit_card_eq y.val.property).trans F.A_card
  have hyfix : ∀ v : F.four, y.val.val.map v.val.val.toMonoidHom = y.val.val := by
    intro v
    exact congrArg Subtype.val (y.property v)
  rcases (fixed_iff_on_lines F y.val.val hycard).mp hyfix with h | h
  · exact h
  · exact (F.nonfusion (h ▸ y.val.property)).elim

/-- The marked A-orbit has odd cardinality by the two-group fixed-point congruence. -/
theorem FourLineFrame.A_orbit_card_mod_two [Finite E] (F : FourLineFrame H) :
    Nat.card {L : Subgroup E // InLineOrbit H F.A L} ≡ 1 [MOD 2] := by
  let : IsElementaryAbelian 2 F.four := F.four_elementary
  have h := (IsElementaryAbelian.isPGroup 2 F.four).card_modEq_card_fixedPoints
    (MulAction.orbit H F.A)
  rw [F.fixedPoints_A_orbit_card] at h
  exact h

/-- The line-stabilizer order bound excludes the remaining order-32 case. -/
theorem FourLineFrame.card_eq_twelve_of_stabilizer_dvd [Finite E]
    [IsElementaryAbelian 5 E] (F : FourLineFrame H)
    (hE : Nat.card E = 25) (hm : Nat.card H ≡ 2 [MOD 5])
    (hstab : Nat.card (MulAction.stabilizer H F.A) ∣ 80) : Nat.card H = 12 := by
  rcases F.card_cases hE hm with h | h
  · exact h
  exfalso
  have hmul := orbit_stabilizer_card (H := H) F.A
  rw [h] at hmul
  have hd : Nat.card (MulAction.orbit H F.A) ∣ 32 := ⟨_, hmul.symm⟩
  have hmem := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hdiv : Nat.divisors 32 = {1, 2, 4, 8, 16, 32} := by decide +kernel
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hodd := F.A_orbit_card_mod_two
  change Nat.card (MulAction.orbit H F.A) % 2 = 1 % 2 at hodd
  have hOrbit : Nat.card (MulAction.orbit H F.A) = 1 := by omega
  rw [hOrbit, one_mul] at hmul
  rw [hmul] at hstab
  norm_num at hstab

private theorem orbit_card_three_of_stabilizer [Finite E] (F : FourLineFrame H)
    (hH : Nat.card H = 12) (L : Subgroup E)
    (hfix : ∀ v : F.four, v.val • L = L)
    (hstab : Nat.card (MulAction.stabilizer H L) ∣ 80) :
    Nat.card (MulAction.orbit H L) = 3 := by
  have hle : F.four ≤ MulAction.stabilizer H L := fun x hx => hfix ⟨x, hx⟩
  have hfour : 4 ∣ Nat.card (MulAction.stabilizer H L) :=
    F.four_card ▸ Subgroup.card_dvd_of_le hle
  have hd : Nat.card (MulAction.stabilizer H L) ∣ 12 :=
    hH ▸ (MulAction.stabilizer H L).card_subgroup_dvd_card
  have hfour' : Nat.card (MulAction.stabilizer H L) ∣ 4 := by
    simpa using Nat.dvd_gcd hd hstab
  have hstabeq := Nat.dvd_antisymm hfour' hfour
  have hmul := orbit_stabilizer_card (H := H) L
  rw [hH, hstabeq] at hmul
  omega

/-- Both marked orbits have size three, once the actor and stabilizers are counted. -/
theorem FourLineFrame.orbit_cards_of_card_twelve [Finite E] (F : FourLineFrame H)
    (hH : Nat.card H = 12)
    (hA : Nat.card (MulAction.stabilizer H F.A) ∣ 80)
    (hB : Nat.card (MulAction.stabilizer H F.B) ∣ 80) :
    Nat.card {L : Subgroup E // InLineOrbit H F.A L} = 3 ∧
      Nat.card {L : Subgroup E // InLineOrbit H F.B L} = 3 :=
  ⟨orbit_card_three_of_stabilizer F hH F.A (fixed_A F) hA,
    orbit_card_three_of_stabilizer F hH F.B (fixed_B F) hB⟩

/-- Two disjoint three-element line orbits exhaust the six lines of the plane. -/
theorem FourLineFrame.coverage_of_orbit_cards [Finite E] (F : FourLineFrame H)
    (h6 : Nat.card {L : Subgroup E // Nat.card L = 5} = 6)
    (hA : Nat.card {L : Subgroup E // InLineOrbit H F.A L} = 3)
    (hB : Nat.card {L : Subgroup E // InLineOrbit H F.B L} = 3) :
    ∀ L : Subgroup E, Nat.card L = 5 → InLineOrbit H F.A L ∨ InLineOrbit H F.B L := by
  have hdisj : Disjoint (MulAction.orbit H F.A) (MulAction.orbit H F.B) := by
    apply Set.disjoint_left.mpr
    intro L hLA hLB
    have heq := (MulAction.orbit_eq_iff.mpr hLA).symm.trans (MulAction.orbit_eq_iff.mpr hLB)
    exact F.nonfusion ((inLineOrbit_iff_mem_orbit F.A F.B).mpr
      (heq.symm ▸ MulAction.mem_orbit_self F.B))
  have hsub : MulAction.orbit H F.A ∪ MulAction.orbit H F.B ⊆
      {L : Subgroup E | Nat.card L = 5} := by
    intro L hL
    rcases hL with hL | hL
    · exact (orbit_card_eq hL).trans F.A_card
    · exact (orbit_card_eq hL).trans F.B_card
  have hcount : (MulAction.orbit H F.A ∪ MulAction.orbit H F.B).ncard = 6 := by
    rw [Set.ncard_union_eq hdisj]
    change Nat.card (MulAction.orbit H F.A) + Nat.card (MulAction.orbit H F.B) = 6
    change Nat.card (MulAction.orbit H F.A) = 3 at hA
    change Nat.card (MulAction.orbit H F.B) = 3 at hB
    omega
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    change Nat.card {L : Subgroup E // Nat.card L = 5} ≤ _
    rw [h6, hcount])
  intro L hL
  exact (heq.symm ▸ hL : L ∈ MulAction.orbit H F.A ∪ MulAction.orbit H F.B)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction
