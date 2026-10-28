module

public import Theory.GroupTheory.IndexTwoCentralizerFixedCard
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# An ambient elementary subgroup with a central omega line

An elementary binary subgroup E inside T, normalized by T and centralized
by an index-two subgroup Q of T, has order at most the square of the order
of Ω1(Z(T)). The genuine involutory fixed-point estimate supplies the square
bound; the common fixed subgroup embeds in the actual ambient central omega.
No assumption that the restriction to a section is faithful is used.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Ambient form of the central omega square bound, retaining the original
actor, its index-two subgroup, and its normalized elementary subgroup. -/
theorem elementary_card_le_omegaCenterIn_sq_of_relIndex_two
    (T Q E : Subgroup G) [IsElementaryAbelian 2 E]
    (hET : E ≤ T) (hTE : T ≤ normalizer (E : Set G))
    (hEQ : E ≤ centralizer (Q : Set G)) (hi : Q.relIndex T = 2) :
    Nat.card E ≤ Nat.card (omegaCenterIn T) ^ 2 := by
  have hs := card_le_centralizer_card_sq_of_relIndex_two E Q T hTE hEQ hi
  let j : (centralizer (T : Set G)).subgroupOf E → omegaCenterIn T :=
    fun x => ⟨x.val.val, (mem_omegaCenterIn_iff T _).mpr
      ⟨hET x.val.property, x.property,
        elemPow_eq_one_of_isElementaryAbelian x.val.val x.val.property⟩⟩
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : omegaCenterIn T => (z : G)) h
  exact hs.trans (Nat.pow_le_pow_left (Nat.card_le_card_of_injective j hj) 2)

/-- A central omega line limits every such elementary subgroup to order four. -/
theorem elementary_card_le_four_of_relIndex_two_omegaCenterIn
    (T Q E : Subgroup G) [IsElementaryAbelian 2 E]
    (hET : E ≤ T) (hTE : T ≤ normalizer (E : Set G))
    (hEQ : E ≤ centralizer (Q : Set G)) (hi : Q.relIndex T = 2)
    (hZ : Nat.card (omegaCenterIn T) = 2) : Nat.card E ≤ 4 := by
  simpa only [hZ, show (2 : ℕ)^2=4 by decide] using
    elementary_card_le_omegaCenterIn_sq_of_relIndex_two T Q E hET hTE hEQ hi

end Subgroup
