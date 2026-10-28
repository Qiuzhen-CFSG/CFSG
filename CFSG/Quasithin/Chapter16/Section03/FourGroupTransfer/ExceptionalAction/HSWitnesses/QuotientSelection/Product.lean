module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# The centralizer of the embedded component in the HS product row

A perfect subgroup of C₂ × Aut(A₆) lies in the normal A₆: the quotient has
order eight and is solvable. If that subgroup has order at least 360, it
therefore equals this A₆. An automorphism commuting with all its inner
automorphisms fixes every element of A₆, so its centralizer injects into C₂.
This keeps track of an arbitrary actual embedding, not just the abstract
isomorphism type of the component.

Source application: Aschbacher–Smith, 16.1.5(10), 16.1.7(3h), and 16.3.5,
printed pp.1172–1173 and 1179.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses.QuotientSelection
open Subgroup Theory.GroupTheory
open OtherPreliminaries.JankoTwoHigmanSims

/-- Every sufficiently large perfect subgroup of the product row has
centralizer of order at most two, for its actual embedding in that product. -/
theorem product_centralizer_card_le_two (K : Subgroup (C2 × MulAut A6)) [Group.IsPerfect K]
    (hK : 360 ≤ Nat.card K) : Nat.card (centralizer (K : Set (C2 × MulAut A6))) ≤ 2 := by
  let N : Subgroup (C2 × MulAut A6) :=
    (⊥ : Subgroup C2).prod AlternatingSix.ShadowLocal.inner
  have hNcard : Nat.card N = 360 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
    simp [AlternatingSix.ShadowLocal.card_inner]
  let : N.Normal := inferInstanceAs ((⊥ : Subgroup C2).prod AlternatingSix.ShadowLocal.inner).Normal
  have hquot : Nat.card ((C2 × MulAut A6) ⧸ N) = 8 := by
    have hc := N.card_mul_index
    rw [hNcard, Nat.card_prod, show Nat.card C2 = 2 by simp [C2],
      AlternatingSix.ShadowLocal.card_aut, index_eq_card] at hc
    omega
  let : Group.IsNilpotent ((C2 × MulAut A6) ⧸ N) :=
    (IsPGroup.of_card (p := 2) (n := 3) hquot).isNilpotent
  have hle : K ≤ N := le_of_isPerfect_of_solvable_quotient K N
  have heq : K = N := eq_of_le_of_card_ge hle (hNcard ▸ hK)
  rw [heq]
  have hsnd (g : centralizer (N : Set (C2 × MulAut A6))) : g.val.2 = 1 := by
    apply MulEquiv.ext
    intro a
    apply AlternatingSix.ShadowLocal.inner_injective
    have hc := mem_centralizer_iff.mp g.property
      (1, MulAut.conj a) (show (1, MulAut.conj a) ∈ N from ⟨by simp, ⟨a, rfl⟩⟩)
    have hm : MulAut.conj a * g.val.2 = g.val.2 * MulAut.conj a := congrArg Prod.snd hc
    calc
      MulAut.conj (g.val.2 a) = g.val.2 * MulAut.conj a * g.val.2⁻¹ := by ext x; simp
      _ = MulAut.conj a := by rw [← hm]; simp [mul_assoc]
  let f : centralizer (N : Set (C2 × MulAut A6)) → C2 := fun g => g.val.1
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (Prod.ext hxy ((hsnd x).trans (hsnd y).symm))
  simpa [C2] using Nat.card_le_card_of_injective f hf

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses.QuotientSelection
