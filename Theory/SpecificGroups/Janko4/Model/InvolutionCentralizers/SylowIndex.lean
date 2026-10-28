module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Placement
public import Theory.SpecificGroups.Janko4.Model.Cardinality

/-!
# J₄ involution centralizers with small Sylow index

A centralizer meeting a Sylow two-subgroup in index at most two belongs
to the first native involution class. Indeed the Sylow order is divisible
by 2²¹, while the second centralizer has two-part 2¹⁷. Even doubling that
centralizer order cannot contain the selected Sylow order. The equivalence
returned is the existing native centralizer equivalence, not a family tag.

This is the precise local order comparison used for the original fixed line
in Aschbacher--Smith, proof of 12.6.12, printed pp.825--826. The model and
centralizer orders are the certified GLS3 Table 5.3i / ATLAS J₄ data.
-/

public section
open Subgroup Theory.GroupTheory
namespace Janko4.InvolutionCentralizers
attribute [local irreducible] modelGroup matrixA matrixB

/-- The smaller native involution centralizer cannot meet a full Sylow in index at most two. -/
theorem centralizer_equiv_first_of_sylow_index_le_two (t : Model) (ht : orderOf t = 2)
    (P : Sylow 2 Model)
    (hi : (centralizer ({t} : Set Model)).relIndex (P : Subgroup Model) ≤ 2) :
    Nonempty (centralizer ({t} : Set Model) ≃* First.centralizer) := by
  rcases centralizer_equiv_first_or_second t ht with h | h
  · exact h
  obtain ⟨e⟩ := h
  exfalso
  let C := centralizer ({t} : Set Model)
  let A := C.subgroupOf (P : Subgroup Model)
  have hd : 2^21 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (by
    rw [Cardinality.model_card]; norm_num)
  have hcard := A.card_mul_index
  have hA : Nat.card A ∣ Nat.card C := by
    let j : A →* C := {
      toFun x := ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact card_dvd_of_injective j (fun x y h => Subtype.ext (Subtype.ext
      (congrArg (fun x : C => (x : Model)) h)))
  have hne : A.index ≠ 0 := index_ne_zero_of_finite
  have hi' : A.index = 1 ∨ A.index = 2 := by change A.index ≤ 2 at hi; omega
  have hc : Nat.card C = 1816657920 := (Nat.card_congr e.toEquiv).trans Second.ambient_card
  rcases hi' with hi' | hi'
  · rw [hi',mul_one] at hcard
    rw [←hcard] at hd
    have hh := hd.trans hA
    rw [hc] at hh
    norm_num at hh
  · rw [hi'] at hcard
    have hh : 2^21 ∣ 1816657920 * 2 := by
      rw [←hc]
      rw [←hcard] at hd
      exact hd.trans (Nat.mul_dvd_mul_right hA 2)
    norm_num at hh
end Janko4.InvolutionCentralizers
