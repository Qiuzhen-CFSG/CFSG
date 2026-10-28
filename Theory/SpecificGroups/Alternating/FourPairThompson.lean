module
public import Theory.SpecificGroups.Alternating.FourPairThompson.Generation
import Mathlib.Tactic
/-!
# Thompson movement forces the full A₄-pair automorphism group

An elementary subgroup of order at least sixteen lies in the base. Its two
coordinate images have order at most four, so it fills their direct product.
If one coordinate contains an odd permutation, independent coordinates and
factor exchange generate the whole wreath product. Thus, in a proper
factor-transitive overgroup of A₄ × A₄, every largest elementary subgroup
of a group containing V₄ × V₄ lies in that Klein four base.

Consequently J(R) lies in V₄ × V₄. The source equation X = [X,J(R)]
would put the order-twelve group X inside a group of order sixteen. This
contradiction proves fullness of the original automorphism image.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 14.1.10,
printed p.978. The final theorem uses precisely the native inputs supplied
by the faithful conjugation action of the source group.
-/
@[expose] public section
namespace AlternatingFourPair.Thompson
open Subgroup

def coordinatePair (E : Subgroup W) (hb : E ≤ base) :
    E →* (evaluation E hb 1).range × (evaluation E hb swapIndex).range :=
  (evaluation E hb 1).rangeRestrict.prod (evaluation E hb swapIndex).rangeRestrict

 theorem coordinatePair_injective (E : Subgroup W) (hb : E ≤ base) :
    Function.Injective (coordinatePair E hb) := by
  intro a b hab
  apply Subtype.ext
  apply RegularWreathProduct.ext
  · funext i
    rcases index_cases i with rfl | rfl
    · exact congrArg (fun p => p.1.val) hab
    · exact congrArg (fun p => p.2.val) hab
  · exact (hb a.property).trans (hb b.property).symm

 theorem coordinatePair_surjective (E : Subgroup W) (hb : E ≤ base)
    (hE : IsElementaryAbelian 2 E) (hc : 16 ≤ Nat.card E) :
    Function.Surjective (coordinatePair E hb) := by
  let _ := hE
  have h1 : Nat.card (evaluation E hb 1).range ≤ 4 :=
    symmetricFour_elementary_card_le _ (IsElementaryAbelian.of_surjective
      (evaluation E hb 1).rangeRestrict (evaluation E hb 1).rangeRestrict_surjective)
  have h2 : Nat.card (evaluation E hb swapIndex).range ≤ 4 :=
    symmetricFour_elementary_card_le _ (IsElementaryAbelian.of_surjective
      (evaluation E hb swapIndex).rangeRestrict (evaluation E hb swapIndex).rangeRestrict_surjective)
  apply ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨coordinatePair_injective E hb, ?_⟩).2
  apply le_antisymm (Nat.card_le_card_of_injective _ (coordinatePair_injective E hb))
  rw [Nat.card_prod]
  exact (Nat.mul_le_mul h1 h2).trans hc

 theorem axis_mem_of_card (E : Subgroup W) (hE : IsElementaryAbelian 2 E)
    (hc : 16 ≤ Nat.card E) (w : W) (hw : w ∈ E) (i : Q) :
    axis i (w.left i) ∈ E := by
  have hb := elementary_le_base_of_card E hE hc
  have hs := coordinatePair_surjective E hb hE hc
  rcases index_cases i with rfl | rfl
  · obtain ⟨z, hz⟩ := hs ((evaluation E hb 1).rangeRestrict ⟨w, hw⟩, 1)
    have h1 : z.val.left 1 = w.left 1 := congrArg (fun p => p.1.val) hz
    have h2 : z.val.left swapIndex = 1 := congrArg (fun p => p.2.val) hz
    have he : z.val = axis 1 (w.left 1) := by
      apply RegularWreathProduct.ext
      · funext i
        rcases index_cases i with rfl | rfl
        · simpa using h1
        · simpa using h2
      · exact hb z.property
    rw [← he]; exact z.property
  · obtain ⟨z, hz⟩ := hs (1, (evaluation E hb swapIndex).rangeRestrict ⟨w, hw⟩)
    have h1 : z.val.left 1 = 1 := congrArg (fun p => p.1.val) hz
    have h2 : z.val.left swapIndex = w.left swapIndex := congrArg (fun p => p.2.val) hz
    have he : z.val = axis swapIndex (w.left swapIndex) := by
      apply RegularWreathProduct.ext
      · funext i
        rcases index_cases i with rfl | rfl
        · simpa using h1
        · simpa using h2
      · exact hb z.property
    rw [← he]; exact z.property

 theorem elementary_le_kleinBase_of_proper (H E : Subgroup W)
    (hA : alternatingBase ≤ H) (ht : ¬ H ≤ base) (hp : H ≠ ⊤)
    (hEH : E ≤ H) (hE : IsElementaryAbelian 2 E) (hc : 16 ≤ Nat.card E) :
    E ≤ kleinBase := by
  let _ := hE
  have hb := elementary_le_base_of_card E hE hc
  intro w hw
  refine ⟨hb hw, fun i => ?_⟩
  have hw2 : w ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian w hw
  have hi2 : w.left i ^ 2 = 1 := by
    simpa [pow_two, show w.right = 1 from hb hw] using
      congrArg (fun z : W => z.left i) hw2
  rw [core_mem_iff]
  refine ⟨?_, hi2⟩
  by_contra ho
  apply hp
  exact eq_top_of_axis H hA ht i (w.left i)
    (hEH (axis_mem_of_card E hE hc w hw i)) ho

 theorem thompson_le_kleinBase (H R : Subgroup W)
    (hA : alternatingBase ≤ H) (ht : ¬ H ≤ base) (hp : H ≠ ⊤)
    (hKR : kleinBase ≤ R) (hRH : R ≤ H) :
    Stellmacher.elementaryAbelianMaxJ R ≤ kleinBase := by
  apply sSup_le
  intro E hE
  apply elementary_le_kleinBase_of_proper H E hA ht hp (hE.1.trans hRH) hE.2.1
  have hh := hE.2.2 kleinBase hKR kleinBase_elementary
  rwa [kleinBase_card] at hh

 theorem eq_top_of_moved_twelve (H R X : Subgroup W)
    (hA : alternatingBase ≤ H) (ht : ¬ H ≤ base)
    (hKR : kleinBase ≤ R) (hRH : R ≤ H)
    (hcard : Nat.card X = 12) (hm : X = ⁅X, Stellmacher.elementaryAbelianMaxJ R⁆) : H = ⊤ := by
  by_contra hp
  have hJ := thompson_le_kleinBase H R hA ht hp hKR hRH
  have hX : X ≤ kleinBase := by
    rw [hm]
    exact (commutator_mono le_rfl hJ).trans (commutator_le_right X kleinBase)
  have hd := Subgroup.card_dvd_of_le hX
  rw [hcard, kleinBase_card] at hd
  norm_num at hd
end AlternatingFourPair.Thompson
