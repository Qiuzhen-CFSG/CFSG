module
public import Theory.GroupTheory.SylowCommutingJoin
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
/-!
# Sylow decomposition in a commuting pair

A two-subgroup contained in a commuting pair and intersecting each factor
in a full Sylow is the product of those intersections. Multiplication of
the two chosen Sylows supplies a Sylow of the join; its maximality gives
the asserted equality with the actual embedded two-subgroup.
Source application: Aschbacher--Smith 10.2.3(4), printed p.747.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]
variable [Finite G]
open CFSG.Quasithin.Chapter1
theorem eq_sup_sylow_intersections_of_commuting (S A B : Subgroup G)
    (hS : IsPGroup 2 S) (hSAB : S ≤ A ⊔ B) (hc : A ≤ centralizer (B : Set G))
    (hA : IsSylowIn 2 (S ⊓ A) A) (hB : IsSylowIn 2 (S ⊓ B) B) :
    S = (S ⊓ A) ⊔ (S ⊓ B) := by
  classical
  obtain ⟨P,hP⟩ := hA
  obtain ⟨Q,hQ⟩ := hB
  let C : Bool → Subgroup G := fun b => if b then A else B
  let R : ∀ b, Sylow 2 (C b) := fun b => by cases b; exact Q; exact P
  have hjoin : (⨆ b, C b) = A ⊔ B := by simp [C,iSup_bool_eq]
  have hcomm : Pairwise (fun i j => ∀ x y : G, x ∈ C i → y ∈ C j → Commute x y) := by
    intro i j hij x y hx hy
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hc hy x hx
    · exact (hc hx y hy).symm
    · exact (hij rfl).elim
  obtain ⟨W,hW⟩ := exists_sylow_iSup_le_of_commuting C hcomm R
    ((S ⊓ A) ⊔ (S ⊓ B)) (by
      intro b
      cases b
      · change (Q : Subgroup B).map B.subtype ≤ _
        rw [hQ]
        exact le_sup_right
      · change (P : Subgroup A).map A.subtype ≤ _
        rw [hP]
        exact le_sup_left)
  have hWI : IsSylowIn 2 ((W : Subgroup (⨆ b, C b : Subgroup G)).map (⨆ b, C b : Subgroup G).subtype) (⨆ b, C b) := ⟨W,rfl⟩
  have he := (isSylowIn_iff.mp hWI).2.2 S hS
    (hW.trans (sup_le inf_le_left inf_le_left)) (hjoin.symm ▸ hSAB)
  exact le_antisymm (he.le.trans hW) (sup_le inf_le_left inf_le_left)
end Subgroup
