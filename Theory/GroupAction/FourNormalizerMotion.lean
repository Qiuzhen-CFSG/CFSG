module

public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A four-group normalizer with nontrivial line motion

An action image of order greater than two cannot preserve a subgroup of
order two in a group of order four. The proof bounds the stabilizer of its
unique nonidentity point, and retains the ambient normalizer element.
-/

public section
open Subgroup

/-- A sufficiently large normalizer action moves every order-two subgroup.
This bounds the action image, not the order of the whole normalizer. -/
theorem exists_normalizer_not_normalizer_of_four_action
    {A : Type*} [Group A] (B L : Subgroup A) [Finite B]
    (hB : Nat.card B = 4) (hLB : L ≤ B) (hL : Nat.card L = 2)
    (haction : 2 < Nat.card B.normalizerMonoidHom.range) :
    ∃ a ∈ normalizer (B : Set A), a ∉ normalizer (L : Set A) := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨l, hl, huniq⟩ := (Nat.card_eq_two_iff' (1 : L)).mp hL
  let b : B := ⟨l, hLB l.property⟩
  have hb : b ≠ 1 := fun h => hl (Subtype.ext (congrArg (fun x : B => (x : A)) h))
  have hfix : ∀ f ∈ B.normalizerMonoidHom.range, f b = b := by
    rintro f ⟨a, rfl⟩
    have ham : (a : A) * (l : A) * (a : A)⁻¹ ∈ L :=
      (mem_normalizer_iff.mp (hn a a.property) l).mp l.property
    let l' : L := ⟨(a : A) * (l : A) * (a : A)⁻¹, ham⟩
    have hne : l' ≠ 1 := by
      intro he
      apply hl
      apply Subtype.ext
      apply (MulAut.conj (a : A)).injective
      exact (congrArg Subtype.val he).trans (map_one (MulAut.conj (a : A))).symm
    apply Subtype.ext
    change (a : A) * (l : A) * (a : A)⁻¹ = (l : A)
    exact congrArg (fun x : L => (x : A)) (huniq l' hne)
  have hbound := card_mulAut_subgroup_le_two_of_fixed_point hB b hb
    B.normalizerMonoidHom.range hfix
  omega
