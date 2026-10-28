module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree
public import Theory.GroupTheory.CenterlessProduct
/-!
# Orders of products of alternating-three blocks

Distinct commuting A₃ blocks are independent because each is centerless.
Their product therefore has order twelve to the number of factors. If the
ambient order is not divisible by twenty-seven, at most two factors occur.
This is the residual-size obstruction for the constrained degree-four
endpoint in Aschbacher--Smith 15.1.22(3), printed pp.1099--1100.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]
/-- The literal commuting product has order twelve to its number of factors. -/
theorem alternatingThree_product_card (F : Set (Subgroup G))
    (hF : ∀ A ∈ F, IsAlternatingBlock A 3)
    (hc : F.Pairwise (fun A B => ⁅A,B⁆ = ⊥)) :
    Nat.card (sSup F : Subgroup G) = 12 ^ Nat.card F := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hcomm : Pairwise fun i j : F => ∀ x y : G, x ∈ i.val → y ∈ j.val → Commute x y := by
    intro i j hne x y hx hy
    have h := (commutator_eq_bot_iff_le_centralizer.mp
      (hc i.property j.property (fun he => hne (Subtype.ext he)))) hx
    exact (mem_centralizer_iff.mp h y hy).symm
  have hind := iSupIndep_of_centerless_of_pairwise_commute (fun i : F => i.val)
    (fun i => (hF i.val i.property).center_eq_bot) hcomm
  have hcard (i : F) : Nat.card i.val = 12 := by
    obtain ⟨e⟩ := (hF i.val i.property).equiv_alternatingFour
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  rw [sSup_eq_iSup',natCard_iSup_of_iSupIndep _ hcomm hind]
  simp only [hcard,Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card]

/-- An ambient group with at most two factors of three permits at most two A₃ blocks. -/
theorem alternatingThree_product_card_le_of_not_dvd
    (F : Set (Subgroup G)) (hF : ∀ A ∈ F, IsAlternatingBlock A 3)
    (hc : F.Pairwise (fun A B => ⁅A,B⁆ = ⊥)) (h27 : ¬ 27 ∣ Nat.card G) :
    Nat.card (sSup F : Subgroup G) ≤ 144 := by
  have he := alternatingThree_product_card F hF hc
  have hn : Nat.card F ≤ 2 := by
    by_contra hn
    have hd : 27 ∣ 12 ^ Nat.card F :=
      dvd_trans (by decide : 27 ∣ 12^3) (pow_dvd_pow 12 (by omega))
    exact h27 ((he.symm ▸ hd).trans (sSup F : Subgroup G).card_subgroup_dvd_card)
  rw [he]
  exact (Nat.pow_le_pow_right (by decide : 0 < 12) hn)
end CFSG.Quasithin.ChapterC
