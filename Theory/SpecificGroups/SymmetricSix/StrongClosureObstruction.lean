module

public import Theory.SpecificGroups.SymmetricSix.Parabolics
public import Theory.GroupTheory.SetStrongClosure

/-!
# A finite strong-closure obstruction in the symmetric six-group

In the standard Sylow of S_6, a transposition forces the other two disjoint
transpositions by strong closure. Their product has a Sylow conjugate that
does not commute with a forced transposition. Three triple-transposition
conjugates multiply to the original transposition, reducing that case to
the same obstruction. All identities involve fixed permutations on six
letters. The result applies through any injective ambient homomorphism;
the strongly closed subgroup need not lie in the symmetric subgroup.

Source: Aschbacher--Smith, Proposition 2.2.2, pp.519--520, inspection of
Lemma 1.1.5(3)(c),(d) (combined manuscript, 1 March 2004).
-/

@[expose] public section
open Subgroup Equiv
open scoped IsMulCommutative
open Theory.SpecificGroups.SymmetricSix

namespace Theory.GroupTheory.AlternatingStrongClosure

def trans : S6 := swap 0 1
def pairLeft : S6 := swap 2 3
def pairRight : S6 := swap 4 5
def cross : S6 := swap 2 4 * swap 3 5
def triple : S6 := trans * pairLeft * pairRight
def toLeft : S6 := swap 0 2 * swap 1 3
def toRight : S6 := swap 0 4 * swap 1 5
def toCross : S6 := swap 0 1 * swap 3 4
def toThird : S6 := swap 0 1 * swap 3 5

theorem trans_toLeft : toLeft⁻¹ * trans * toLeft = pairLeft := by decide +kernel
theorem trans_toRight : toRight⁻¹ * trans * toRight = pairRight := by decide +kernel
theorem pair_toCross : toCross⁻¹ * (pairLeft * pairRight) * toCross = cross := by decide +kernel
theorem triple_product : triple * (toCross⁻¹ * triple * toCross) *
    (toThird⁻¹ * triple * toThird) = trans := by decide +kernel
theorem pairLeft_cross_ne : pairLeft * cross ≠ cross * pairLeft := by decide +kernel
theorem trans_mem : trans ∈ borel := by decide +kernel
theorem pairLeft_mem : pairLeft ∈ borel := by decide +kernel
theorem pairRight_mem : pairRight ∈ borel := by decide +kernel
theorem cross_mem : cross ∈ borel := by decide +kernel
theorem triple_toCross_mem : toCross⁻¹ * triple * toCross ∈ borel := by decide +kernel
theorem triple_toThird_mem : toThird⁻¹ * triple * toThird ∈ borel := by decide +kernel

private theorem forced_conjugate {G : Type*} [Group G]
    (S U : Subgroup G) (hU : IsStronglyClosedSet (U : Set G) S ⊤)
    (f : S6 →* G) (hB : borel.map f ≤ S) (x : S6) (hx : f x ∈ U)
    (g : S6) (hxg : g⁻¹ * x * g ∈ borel) : f (g⁻¹ * x * g) ∈ U := by
  have hmem := hB (mem_map_of_mem f hxg)
  simp only [map_mul, map_inv] at hmem ⊢
  exact hU.2 (f x) hx (f g) (mem_top _) hmem

/-- An embedded standard Sylow configuration and its transposition violate
abelian strong closure. U need not lie in the symmetric subgroup. -/
theorem false_of_transposition_embedding {G : Type*} [Group G]
    (S U : Subgroup G) [IsMulCommutative U]
    (hU : IsStronglyClosedSet (U : Set G) S ⊤)
    (f : S6 →* G) (hf : Function.Injective f) (hB : borel.map f ≤ S)
    (ht : f trans ∈ U) : False := by
  have hL : f pairLeft ∈ U := by
    rw [← trans_toLeft]
    exact forced_conjugate S U hU f hB trans ht toLeft (trans_toLeft.symm ▸ pairLeft_mem)
  have hR : f pairRight ∈ U := by
    rw [← trans_toRight]
    exact forced_conjugate S U hU f hB trans ht toRight (trans_toRight.symm ▸ pairRight_mem)
  have hLR : f (pairLeft * pairRight) ∈ U := by rw [map_mul]; exact mul_mem hL hR
  have hC : f cross ∈ U := by
    rw [← pair_toCross]
    exact forced_conjugate S U hU f hB (pairLeft * pairRight) hLR toCross
      (pair_toCross.symm ▸ cross_mem)
  apply pairLeft_cross_ne
  apply hf
  rw [map_mul, map_mul]
  exact congrArg Subtype.val (mul_comm (⟨f pairLeft, hL⟩ : U) ⟨f cross, hC⟩)

/-- Three forced triple-transposition conjugates multiply to a transposition,
so the same short fusion obstruction applies. -/
theorem false_of_triple_embedding {G : Type*} [Group G]
    (S U : Subgroup G) [IsMulCommutative U]
    (hU : IsStronglyClosedSet (U : Set G) S ⊤)
    (f : S6 →* G) (hf : Function.Injective f) (hB : borel.map f ≤ S)
    (ht : f triple ∈ U) : False := by
  have hC := forced_conjugate S U hU f hB triple ht toCross triple_toCross_mem
  have hD := forced_conjugate S U hU f hB triple ht toThird triple_toThird_mem
  apply false_of_transposition_embedding S U hU f hf hB
  rw [← triple_product, map_mul, map_mul]
  exact mul_mem (mul_mem ht hC) hD

end Theory.GroupTheory.AlternatingStrongClosure
