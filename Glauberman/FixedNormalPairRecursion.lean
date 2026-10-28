module
public import Glauberman.FixedNormalPairTerminal

/-!
# Finite descent of the fixed-normal-free intersection pair

The natural omega action supplies a uniform fixed-index lower bound four.
The counting and terminal replacement theorems prove that either the old
intersection is elementary abelian, or its literal preimage and itself form
a new pair with the same numerical properties. Both new quotient indices
remain four, so the size decreases strictly. Iteration therefore reaches an
elementary intersection. No new natural-module recognition is assumed at a
recursive row; the original action marking remains available to later steps.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition4.4 and
Lemma4.5, printedpp45–46. This module retains their numerical recursion and
actual subgroup maps, not the stronger full module-section hypothesis.
-/

public section
open Subgroup Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G]

/-- The numerical consequence of the natural module condition used in the
recursive pair argument. All subgroups and maps remain in the original group. -/
structure NumericalPair (S T : Subgroup G) (φ : S ≃* T) : Prop where
  two : IsPGroup 2 S
  no_fixed : ∀ A : Subgroup S, A.Normal →
    (A.map φ.toMonoidHom).map T.subtype = A.map S.subtype → A = ⊥
  normal_left : S ≤ normalizer (S ⊓ T : Set G)
  normal_right : T ≤ normalizer (S ⊓ T : Set G)
  index_left : (S ⊓ T).relIndex S = 4
  index_right : (S ⊓ T).relIndex T = 4
  lower_left : ∀ B : Subgroup G, B ≤ S → ¬ B ≤ S ⊓ T →
    4 ≤ (omegaCenterIn (S ⊓ T) ⊓ centralizer (B : Set G)).relIndex (omegaCenterIn (S ⊓ T))
  lower_right : ∀ B : Subgroup G, B ≤ T → ¬ B ≤ S ⊓ T →
    4 ≤ (omegaCenterIn (S ⊓ T) ⊓ centralizer (B : Set G)).relIndex (omegaCenterIn (S ⊓ T))

/-- Literal restriction of the pair isomorphism to the preimage of the
intersection, with its codomain identified with that intersection. -/
@[expose] noncomputable def nextPairEquiv {S T : Subgroup G} (φ : S ≃* T) :
    image φ.symm (S ⊓ T) ≃* ↥(S ⊓ T) :=
  (imageEquiv φ (image φ.symm (S ⊓ T)) (image_le φ.symm _)).trans
    (MulEquiv.subgroupCongr (image_symm φ.symm (S ⊓ T) inf_le_right))

theorem nextPairEquiv_apply {S T : Subgroup G} (φ : S ≃* T)
    (x : image φ.symm (S ⊓ T)) :
    (nextPairEquiv φ x : G) = (φ ⟨x,image_le φ.symm _ x.property⟩ : G) := rfl

private theorem relative_index_of_normal_supplement {S Q R : Subgroup G}
    (hRS : R ≤ S) (hQS : Q ≤ S) (hn : S ≤ normalizer (Q : Set G))
    (hgen : R ⊔ Q = S) : (R ⊓ Q).relIndex R = Q.relIndex S := by
  let _ : (Q.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer hn
  have hh := relIndex_sup_right (R.subgroupOf S) (Q.subgroupOf S)
  rw [←subgroupOf_sup hRS hQS,relIndex_subgroupOf (sup_le hRS hQS),
    relIndex_subgroupOf hRS,hgen] at hh
  rw [inf_relIndex_left]
  exact hh.symm

private theorem relIndex_image {S T : Subgroup G} (φ : S ≃* T)
    (R Q : Subgroup G) (hQS : Q ≤ S) :
    (image φ R).relIndex (image φ Q) = R.relIndex Q := by
  rw [image,image,relIndex_map_map_of_injective _ _ (ambientHom_injective φ),
    relIndex_subgroupOf hQS]

private theorem next_no_fixed {S T : Subgroup G} (φ : S ≃* T)
    (hno : ∀ A : Subgroup S, A.Normal →
      (A.map φ.toMonoidHom).map T.subtype = A.map S.subtype → A = ⊥)
    (hgen : image φ.symm (S ⊓ T) ⊔ (S ⊓ T) = S)
    (A : Subgroup (image φ.symm (S ⊓ T))) (hA : A.Normal)
    (hfix : (A.map (nextPairEquiv φ).toMonoidHom).map (S ⊓ T).subtype =
      A.map (image φ.symm (S ⊓ T)).subtype) : A = ⊥ := by
  let _ := hA
  apply restricted_pair_no_fixed_normal φ hno _ (image_le φ.symm _)
    (by
      have hm : image φ (image φ.symm (S ⊓ T)) = S ⊓ T :=
        image_symm φ.symm (S ⊓ T) inf_le_right
      rw [hm]
      exact hgen) A
  rw [map_map] at hfix ⊢
  exact hfix

/-- One recursive step: either the old intersection is elementary abelian,
or the literal restricted pair satisfies the same numerical hypotheses. -/
theorem NumericalPair.recursion [Finite G] {S T : Subgroup G} {φ : S ≃* T}
    (h : NumericalPair S T φ) :
    IsElementaryAbelian 2 ↥(S ⊓ T) ∨
      (NumericalPair (image φ.symm (S ⊓ T)) (S ⊓ T) (nextPairEquiv φ) ∧
        image φ.symm (S ⊓ T) ⊔ (S ⊓ T) = S) := by
  by_cases hQ : S ⊓ T = ⊥
  · left
    rw [hQ]
    refine ⟨?_⟩
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun _ => Subsingleton.elim _ _)
  have hS : S ≠ ⊥ := fun he => hQ (le_bot_iff.mp (inf_le_left.trans he.le))
  let Q := S ⊓ T
  let R := image φ.symm Q
  have hRS : R ≤ S := image_le φ.symm Q
  have hRmap : image φ R = Q := image_symm φ.symm Q inf_le_right
  have hRn : S ≤ normalizer (R : Set G) := normalizes_image φ.symm Q inf_le_right h.normal_right
  obtain ⟨_,_,hreplaceS,hreplaceT,hfamilyS,hfamilyT,_,_⟩ :=
    fixed_normal_pair_counting S T (omegaCenterIn Q) φ hS h.no_fixed
      h.normal_left h.normal_right
      (fun _ hx => ((mem_omegaCenterIn_iff Q _).mp hx).1) inferInstance
      (fun _ hx => ((mem_omegaCenterIn_iff Q _).mp hx).2.1)
      (fun B hB hBQ => by rw [h.index_left]; exact h.lower_left B hB.1 hBQ)
      (fun B hB hBQ => by rw [h.index_right]; exact h.lower_right B hB.1 hBQ)
  have hgen : R ⊔ Q = S := preimage_intersection_generates φ h.no_fixed hQ
    h.normal_right hfamilyT (fun B hB hBQ => (hreplaceS B hB hBQ).1)
  by_cases hcommon : ∃ A, A ∈ thompsonAbelianSubgroups S ∧ A ≤ R ⊓ Q
  · obtain ⟨A,hA,hAD⟩ := hcommon
    obtain ⟨hlowerR,hlowerQ⟩ := both_fixedIndex_lower_of_common_maximum S T φ R A
      hRS hRmap rfl hA hAD h.lower_left h.lower_right
    have hDn : S ≤ normalizer (R ⊓ Q : Set G) :=
      fun x hx => inf_normalizer_le_normalizer_inf ⟨hRn hx,h.normal_left hx⟩
    have hidxR : (R ⊓ Q).relIndex R = 4 :=
      (relative_index_of_normal_supplement hRS inf_le_left h.normal_left hgen).trans h.index_left
    have hidxQ : (R ⊓ Q).relIndex Q = 4 := by
      rw [inf_comm]
      rw [relative_index_of_normal_supplement inf_le_left hRS hRn ((sup_comm Q R).trans hgen)]
      have hh := relIndex_image φ R S le_rfl
      rw [hRmap,image_self] at hh
      exact hh.symm.trans h.index_right
    exact Or.inr ⟨⟨h.two.of_injective (inclusion hRS) (inclusion_injective hRS),
      next_no_fixed φ h.no_fixed hgen,hRS.trans hDn,inf_le_left.trans hDn,
      hidxR,hidxQ,hlowerR,hlowerQ⟩,hgen⟩
  · left
    exact elementary_intersection_of_no_common_maximum S T φ R h.no_fixed h.two
      hRS hRmap rfl h.normal_left h.normal_right hfamilyS hfamilyT
      (fun A hA hAD => hcommon ⟨A,hA,hAD⟩) hreplaceS hreplaceT
/-- An actual pair with its specified isomorphism, used to iterate the
restriction without replacing either member by an abstract group. -/
structure IntersectionPair (G : Type*) [Group G] where
  left : Subgroup G
  right : Subgroup G
  equiv : left ≃* right

namespace IntersectionPair
@[expose] noncomputable def next (P : IntersectionPair G) : IntersectionPair G :=
  ⟨image P.equiv.symm (P.left ⊓ P.right),P.left ⊓ P.right,nextPairEquiv P.equiv⟩

@[expose] noncomputable def row (P : IntersectionPair G) : ℕ → IntersectionPair G
  | 0 => P
  | n + 1 => P.next.row n

@[simp] theorem row_zero (P : IntersectionPair G) : P.row 0 = P := rfl
@[simp] theorem row_succ (P : IntersectionPair G) (n : ℕ) :
    P.row (n + 1) = P.next.row n := rfl

theorem next_left_le (P : IntersectionPair G) : P.next.left ≤ P.left :=
  image_le P.equiv.symm _

theorem next_card_left [Finite G] (P : IntersectionPair G) :
    Nat.card P.next.left = Nat.card ↥(P.left ⊓ P.right) :=
  Nat.card_congr (nextPairEquiv P.equiv).toEquiv

/-- Every successful recursion strictly reduces the size of the left member. -/
theorem next_card_lt [Finite G] (P : IntersectionPair G)
    (h : NumericalPair P.left P.right P.equiv) : Nat.card P.next.left < Nat.card P.left := by
  rw [next_card_left]
  apply lt_of_le_of_ne (card_le_of_le inf_le_left)
  intro he
  have hQ := eq_of_le_of_card_ge (inf_le_left : P.left ⊓ P.right ≤ P.left) he.ge
  have hi : (P.left ⊓ P.right).relIndex P.left = 1 := relIndex_eq_one.mpr hQ.ge
  have := h.index_left
  omega

/-- The original finite intersection sequence reaches an elementary row.
This is the numerical form of Niles4.5, obtained from the proved4.4 recursion. -/
theorem exists_elementary_row [Finite G] (P : IntersectionPair G)
    (h : NumericalPair P.left P.right P.equiv) :
    ∃ n, IsElementaryAbelian 2 ↥((P.row n).left ⊓ (P.row n).right) := by
  generalize he : Nat.card P.left = m
  induction m using Nat.strong_induction_on generalizing P with
  | h m ih =>
    rcases h.recursion with hE | ⟨hnext,_⟩
    · exact ⟨0,hE⟩
    · obtain ⟨n,hn⟩ := ih (Nat.card P.next.left) (he ▸ P.next_card_lt h) P.next hnext rfl
      exact ⟨n + 1,hn⟩
end IntersectionPair

end Glauberman
