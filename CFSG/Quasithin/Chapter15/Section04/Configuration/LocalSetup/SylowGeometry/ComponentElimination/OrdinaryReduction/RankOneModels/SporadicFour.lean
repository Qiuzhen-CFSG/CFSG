module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.SporadicFour.JankoFour
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.SporadicFour.JankoTwo
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.SporadicFour.Held
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.SporadicFour.Rudvalis

/-!
# Structural separation of four sporadic carriers from ordinary PSL₂

Odd prime-power subgroups of the ordinary rank-one models are cyclic.
The actual J₂, J₄ and He carriers have checked noncyclic three-subgroups,
and the Ru carrier has a checked noncyclic five-subgroup. These witnesses
give the four exclusions, without ambient order or simplicity assumptions.
The unconditional `sporadic_four_separation` supplies exactly the `hfour`
premise of `ComponentElimination.rank_one_models_of_comparisons`.

Source: Aschbacher–Smith, full 1.1.5(3)(f), printed pp.501–503, used in
the proof of 15.4.20, printed p.1164. The carriers are exactly those of
`ClassificationModels.SporadicName.Carrier`.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
open ClassificationModels

/-- Noncyclic odd subgroups in the three remaining carriers suffice for
the exact four-name comparison. The J₄ witness is already discharged. -/
theorem sporadic_four_separation_of_subgroups
    (hj2 : ∃ P : Subgroup Sporadic.LeechRelated.J2.Carrier,
      IsPGroup 3 P ∧ ¬ IsCyclic P)
    (hhe : ∃ P : Subgroup Held.He, IsPGroup 3 P ∧ ¬ IsCyclic P)
    (hru : ∃ P : Subgroup Rudvalis.Model, IsPGroup 5 P ∧ ¬ IsCyclic P)
    (name : SporadicName)
    (hname : name = .j2 ∨ name = .j4 ∨ name = .he ∨ name = .ru)
    {q : ℕ} (hq : (∃ n : ℕ, Even n ∧ q = 2^n) ∨ q.Prime ∧ Odd q) :
    ¬ ClassicalGroup.IsPSL name.Carrier 2 q := by
  rcases hname with rfl | rfl | rfl | rfl
  · obtain ⟨P, hP, hnc⟩ := hj2
    intro hm
    exact hnc (ordinary_rank_one_odd_subgroup_cyclic (r := 3) (by decide) P hP hq hm)
  · exact j4_rank_one_separation hq
  · obtain ⟨P, hP, hnc⟩ := hhe
    intro hm
    exact hnc (ordinary_rank_one_odd_subgroup_cyclic (r := 3) (by decide) P hP hq hm)
  · obtain ⟨P, hP, hnc⟩ := hru
    intro hm
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact hnc (ordinary_rank_one_odd_subgroup_cyclic (r := 5) (by decide) P hP hq hm)

/-- The four fixed sporadic carriers cannot be ordinary rank-one models.
All concrete noncyclic-subgroup witnesses are discharged. -/
theorem sporadic_four_separation
    (name : SporadicName)
    (hname : name = .j2 ∨ name = .j4 ∨ name = .he ∨ name = .ru)
    {q : ℕ} (hq : (∃ n : ℕ, Even n ∧ q = 2^n) ∨ q.Prime ∧ Odd q) :
    ¬ ClassicalGroup.IsPSL name.Carrier 2 q :=
  sporadic_four_separation_of_subgroups j2_noncyclic_three_subgroup
    held_noncyclic_three_subgroup rudvalis_noncyclic_five_subgroup name hname hq

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
