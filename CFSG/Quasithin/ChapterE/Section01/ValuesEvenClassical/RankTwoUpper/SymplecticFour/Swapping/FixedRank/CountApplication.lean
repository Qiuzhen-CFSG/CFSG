module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.FixedRank
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SwappingFixedRank.CenterCount

/-!
# Fixed-actor rank with the center counts discharged

The model calculation counts the literal fixed center of every Sylow-normalizing
swapping automorphism, including arbitrary inner twists and arbitrary orders.
It supplies both cardinality estimates in the rank argument. Only the independent
placement of fixed involutions in the Sylow center remains explicit.

Source: Aschbacher--Smith E.1.1--2 and E.1.14(1), printed pp.209--210,214.
The central-placement producer and the final unconditional assembly belong to
the separate swapping fixed-rank development.
-/

public section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.FixedRank
open DiagramAutomorphisms DiagramAutomorphisms.SwappingFixedRank
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The fixed-center counts are proved; only central placement remains. -/
theorem rank_le_of_central_placement {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    [IsSimpleGroup (generalizedFitting G)]
    (e : Sp F ≃* generalizedFitting G) (hq : 2 < Nat.card F)
    (hplacement : ∀ (S : Sylow 2 (Sp F)) (a : MulAut (Sp F)),
      (S : Subgroup (Sp F)).map a.toMonoidHom = S → ¬ PreservesDiagram a →
      ∀ u ∈ (S : Subgroup (Sp F)), u ^ 2 = 1 → a u = u →
        u ∈ (center S).map (S : Subgroup (Sp F)).subtype)
    (T : Sylow 2 G) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hAH : A ≤ diagramKernel _ e hq)
    (x : G) (hxT : x ∈ (T : Subgroup G))
    (hx : ¬ PreservesDiagram (extensionAction _ e x))
    (hcx : x ∈ centralizer (A : Set G)) : Group.rank A ≤ f := by
  exact rank_le_of_central_root_calculations hF hf e hq hplacement
    (fun S a hS ha => fixedCenter_card_bounds hF hf S a hS ha)
    T A hA hAT hAH x hxT hx hcx

/-- The resulting literal ambient tau containment, conditional only on placement. -/
theorem tau_le_of_central_placement {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    [IsSimpleGroup (generalizedFitting G)]
    (e : Sp F ≃* generalizedFitting G) (hq : 2 < Nat.card F)
    (hplacement : ∀ (S : Sylow 2 (Sp F)) (a : MulAut (Sp F)),
      (S : Subgroup (Sp F)).map a.toMonoidHom = S → ¬ PreservesDiagram a →
      ∀ u ∈ (S : Subgroup (Sp F)), u ^ 2 = 1 → a u = u →
        u ∈ (center S).map (S : Subgroup (Sp F)).subtype)
    (T : Sylow 2 G) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAT : A ≤ (T : Subgroup G))
    (hAH : A ≤ diagramKernel _ e hq) (hr : f < Group.rank A) :
    tau (T : Subgroup G) A ≤ diagramKernel _ e hq := by
  exact tau_le_of_central_root_calculations hF hf e hq hplacement
    (fun S a hS ha => fixedCenter_card_bounds hF hf S a hS ha)
    T hLT A hA hAT hAH hr

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.FixedRank
