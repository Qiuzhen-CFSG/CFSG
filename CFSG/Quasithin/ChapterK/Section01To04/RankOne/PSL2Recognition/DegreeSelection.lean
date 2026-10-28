module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.Preparation
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.DegreeSelection.Inner
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.DegreeSelection.Outer

/-!
# Degree selection from the actual Chapter K actor

The inner-actor branch is unconditional: any elementary ratio-two subgroup
inside the literal layer forces degree `2*r`. In particular this settles all
odd defining degrees, since the actual quotient has order dividing `r`.
For an elementary cubic actor outside the layer, the defining degree is even.
The outer-actor estimate splits according to its action on the actual layer
Schur algebra. Combining these branches proves the unconditional degree window
`dim V ≤ 2*(r+1)` from the original cubic-ratio hypothesis. The earlier
conditional reduction is retained, and the final theorem discharges its premise.

Source: Aschbacher–Smith, K.3.1, printed pp.453–454, with the standing
hypotheses on p.451; Guralnick–Malle, Classification of 2F-modules II,
Proposition 4.1, manuscript pp.21–22.
-/

public section
open scoped MatrixGroups
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
namespace CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  {K : Type*} [Field K] [Finite K] [CharP K 2]
  (h : SourceHypotheses ρ L) (e : L ≃* SL(2,K))

include h e

/-- Source reduction with the even-degree outer-actor estimate explicit.
The unconditional theorem below supplies that estimate on the actual ambient
action. -/
theorem psl2_degree_window_of_outer_estimate {r : ℕ} (hr : 2 ≤ r)
    (hc : Nat.card K = 2 ^ r)
    (houter : Even r → ∀ A : Subgroup G, IsElementaryTwo A → IsCubic ρ A →
      fixedCodim ρ A ≤ 2 * rank A → rank A ≤ r → ¬ A ≤ L →
        Module.finrank (ZMod 2) V ≤ 2 * (r + 1)) :
    Module.finrank (ZMod 2) V ≤ 2 * (r + 1) := by
  obtain ⟨A, hA, hC, hd, hR⟩ := h.psl2_cubic_actor e hr hc
  by_cases hi : A ≤ L
  · rw [h.psl2_degree_eq_of_inner_actor e (by omega) hc hA hi hd]
    omega
  · have heven : Even r := by
      rcases Nat.even_or_odd r with heven | hodd
      · exact heven
      · let : IsElementaryAbelian 2 A := hA.2
        exact False.elim (hi (h.psl2_twoSubgroup_le_of_odd e hc hodd
          (IsElementaryAbelian.isPGroup 2 A)))
    exact houter heven A hA hC hd hR hi

/-- The degree window for the actual Chapter K PSL₂ action. The source cubic
actor is either inner, giving dimension `2*r`, or outer at even defining
degree, where the Schur-algebra branches give the required bound. No degree,
module-recognition, or stronger actor hypothesis is assumed. -/
theorem psl2_degree_window {r : ℕ} (hr : 2 ≤ r)
    (hc : Nat.card K = 2 ^ r) :
    Module.finrank (ZMod 2) V ≤ 2 * (r + 1) := by
  apply h.psl2_degree_window_of_outer_estimate e hr hc
  intro heven A hA hC hd hR hAL
  exact h.psl2_degree_window_of_outer_actor e hr hc heven hA hC hd hR hAL

end CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
