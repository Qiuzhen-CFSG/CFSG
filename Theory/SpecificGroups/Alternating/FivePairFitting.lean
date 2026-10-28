module
public import Theory.SpecificGroups.Alternating.FiveSquareFitting
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Two alternating-five components in the generalized Fitting subgroup

Distinct components commute. Their trivial centers make their intersection
trivial, so multiplication identifies their join with A₅ × A₅. If this join
is the generalized Fitting subgroup, the whole group embeds in its actual
automorphism group, whose order is prime to seven.

This supplies the exchanged-component comparison in Aschbacher--Smith
12.9.4, printed p.859, for the literal G.11.2(12) representation row.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.Alternating.FivePairFitting
open FiveSquareAutomorphisms
/-- The join of two distinct A₅ components is their direct product. -/
theorem pair_equiv {D : Type*} [Group D] [Finite D]
    (A B : Subgroup D) (hA : IsComponent D A) (hB : IsComponent D B)
    (hne : A ≠ B) (eA : A ≃* Alt) (eB : B ≃* Alt) :
    Nonempty ((A ⊔ B : Subgroup D) ≃* Pair) := by
  have hZ : center A = ⊥ := by
    apply le_bot_iff.mp
    intro a ha
    have hh := (centerCongr eA ⟨a,ha⟩).property
    change eA a ∈ center Alt at hh
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
    exact eA.injective (hh.trans eA.map_one.symm)
  have hc : A ≤ centralizer (B : Set D) :=
    commutator_eq_bot_iff_le_centralizer.mp (hA.commutator_eq_bot_of_ne hB hne)
  have hd : Disjoint A B := by
    apply disjoint_def.mpr
    intro x hxA hxB
    have hz : (⟨x,hxA⟩ : A) ∈ center A := mem_center_iff.mpr fun a =>
      Subtype.ext ((hc a.property x hxB).symm)
    exact congrArg Subtype.val (show (⟨x,hxA⟩ : A) = 1 from mem_bot.mp (hZ ▸ hz))
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  exact ⟨e.symm.trans (eA.prodCongr eB)⟩

/-- A group with this generalized Fitting subgroup has no seven-section. -/
theorem seven_not_dvd {D : Type*} [Group D] [Finite D]
    (A B : Subgroup D) (hA : IsComponent D A) (hB : IsComponent D B)
    (hne : A ≠ B) (eA : A ≃* Alt) (eB : B ≃* Alt)
    (he : generalizedFitting D = A ⊔ B) : ¬ 7 ∣ Nat.card D := by
  obtain ⟨e⟩ := pair_equiv A B hA hB hne eA eB
  exact FiveSquareFitting.seven_not_dvd ((MulEquiv.subgroupCongr he).trans e)
end Theory.SpecificGroups.Alternating.FivePairFitting
