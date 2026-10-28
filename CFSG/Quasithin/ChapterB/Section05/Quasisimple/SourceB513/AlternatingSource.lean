module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.Alternating
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# B.5.13 for the actual alternating source branches

The marked natural component has order 360 or 20160. The B.5.1 outer list,
together with the same section's dimension, leaves only S₆ or S₈, so the
component has index at most two. This discharges the index premise of the
moved-space argument on the original representation and literal dual.

Source: Aschbacher–Smith, B.5.1 and B.5.13, printed pp.99 and 111–112.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceB513
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

private theorem natural_dimension {n : ℕ} (hlo : 5 ≤ n) (hhi : n ≤ 8) :
    Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin n)) =
      if n = 5 ∨ n = 6 then 4 else 6 := by
  interval_cases n <;>
    first
    | simpa using BinaryPermutation.finrank_natural_odd (Fin _) (by decide)
    | simpa using BinaryPermutation.finrank_natural_even (Fin _) (by decide)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem alternating_source_index_le_two {n : ℕ} (hn : n = 6 ∨ n = 8)
    (s : MovedSection ρ L) (hnat : IsAlternatingNatural (s.action.comp L.subtype) n)
    (hext : L = ⊤ ∨ OuterNaturalAction s.action) : L.index ≤ 2 := by
  rcases hext with rfl | hext
  · simp
  obtain ⟨e⟩ := hnat
  have hlcard : Nat.card L = n.factorial / 2 := by
    rcases hn with rfl | rfl <;>
      rw [Nat.card_congr e.groupEquiv.toEquiv, nat_card_alternatingGroup,
        Nat.card_fin]
  have hmul := L.index_mul_card
  rw [hlcard] at hmul
  have hdim := e.linearEquiv.finrank_eq
  rcases hext with ⟨m, hm5, hm8, ⟨em⟩⟩ | ⟨em⟩
  · have hdimm := em.linearEquiv.finrank_eq
    rw [natural_dimension hm5 hm8] at hdimm
    have hcard : Nat.card G = m.factorial := by
      rw [Nat.card_congr em.groupEquiv.toEquiv, Nat.card_perm, Nat.card_fin]
    rw [hcard] at hmul
    rcases hn with rfl | rfl <;>
      rw [BinaryPermutation.finrank_natural_even (Fin _) (by decide)] at hdim <;>
      norm_num only [Fintype.card_fin] at hdim <;>
      interval_cases m <;> norm_num at hmul hdimm <;> omega
  · obtain ⟨em⟩ := em
    have hcard : Nat.card G = 12096 := by
      rw [Nat.card_congr em.groupEquiv.toEquiv, Atlas.G2.card_Model,
        Nat.card_eq_fintype_card, ZMod.card]
      norm_num
    rw [hcard] at hmul
    have hdimG := em.linearEquiv.finrank_eq
    rw [Atlas.G2.Natural.finrank_space] at hdimG
    rcases hn with rfl | rfl <;>
      rw [BinaryPermutation.finrank_natural_even (Fin _) (by decide)] at hdim <;>
      norm_num only [Fintype.card_fin] at hdim <;>
      norm_num at hmul <;> omega

/-- The complete nonsplit A₆/A₈ numerical branch from the corrected B.5.1
source conclusion. Both the component index and moved-cover premises are
discharged here, for the literal contragredient action. -/
theorem quadraticRatio_le_two_of_alternating_source
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ.dual L)
    (hns : ¬ IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ.dual L))
    {n : ℕ} (hn : n = 6 ∨ n = 8)
    (hnat : IsAlternatingNatural (c.sectionData.action.comp L.subtype) n)
    (hff : IsFFModule ρ.dual) : quadraticRatio ρ ≤ 2 := by
  have hext : L = ⊤ ∨ OuterNaturalAction c.sectionData.action := by
    cases c.clause_one with
    | irreducible _ _ _ _ he => exact he.imp_right And.right
    | doubleThree _ hL _ _ _ => exact Or.inl hL
    | naturalDual _ _ hL _ => exact Or.inl hL
    | repeatedNatural _ _ _ _ _ hL _ => exact Or.inl hL
  let : L.Normal := c.fitting_eq ▸ inferInstance
  exact quadraticRatio_le_two_of_alternating_moved hn c.sectionData (c.clause_two hns).1
    hnat (alternating_source_index_le_two hn c.sectionData hnat hext) hff

end CFSG.Quasithin.ChapterB.SourceB513
