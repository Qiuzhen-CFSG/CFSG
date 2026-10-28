module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.FixedRank
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SwappingFixedRank.CenterPlacement

/-!
# Applying the central placement calculation

The model theorem places every fixed square-one element of a swapping actor in
the actual Sylow center. This file supplies that premise to the fixed-rank
assembly; the independent fixed-center count remains explicit.
-/

public section

open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.FixedRank
open DiagramAutomorphisms DiagramAutomorphisms.SwappingFixedRank
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

theorem rank_le_of_central_root_calculations_of_center_placement {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    [IsSimpleGroup (generalizedFitting G)]
    (e : Sp F ≃* generalizedFitting G) (hq : 2 < Nat.card F)
    (hcount : ∀ (S : Sylow 2 (Sp F)) (a : MulAut (Sp F)),
      (S : Subgroup (Sp F)).map a.toMonoidHom = S → ¬ PreservesDiagram a →
      Nat.card (fixedCenter S a) ≤ Nat.card F ∧
        (Even f → Nat.card (fixedCenter S a) ^ 2 ≤ Nat.card F))
    (T : Sylow 2 G) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hAH : A ≤ diagramKernel _ e hq)
    (x : G) (hxT : x ∈ (T : Subgroup G))
    (hx : ¬ PreservesDiagram (extensionAction _ e x))
    (hcx : x ∈ centralizer (A : Set G)) : Group.rank A ≤ f := by
  refine rank_le_of_central_root_calculations hF hf e hq ?_ hcount
    T A hA hAT hAH x hxT hx hcx
  intro S a hS ha u hu hu2 hfix
  exact Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SwappingFixedRank.central_placement
    hF hf S a hS ha (u := u) hu hu2 hfix

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.FixedRank
