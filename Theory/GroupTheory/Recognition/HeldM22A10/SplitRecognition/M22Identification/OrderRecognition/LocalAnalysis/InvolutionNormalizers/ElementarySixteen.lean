module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.ModelSylow
/-!
# Elementary subgroups of order sixteen in the Case II Sylow group

An involution outside E and F has only twelve commuting square-one
coordinates in T. An elementary subgroup of order sixteen cannot contain
it, so such a subgroup lies in the union E ∪ F. A subgroup contained in a
union of two subgroups lies in one of them; their equal orders give equality.
This avoids enumerating the subgroup lattice.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 1, p.4.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm
local instance : DecidablePred (· ∈ modelE) := fun x =>
  inferInstanceAs (Decidable (x.right = 1))
local instance : DecidablePred (· ∈ modelF) := fun x =>
  decidable_of_iff (x * d = d * x) mem_centralizer_singleton_iff.symm
local instance : DecidablePred (· ∈ modelT) := fun x =>
  decidable_of_iff (x.right * a.right = a.right * x.right) mem_centralizer_singleton_iff.symm

private def commutingSquares (x : TwistedModel) : Finset TwistedModel :=
  Finset.univ.filter fun y => y ∈ modelT ∧ y ^ 2 = 1 ∧ y * x = x * y

private theorem commutingSquares_card : ∀ x : TwistedModel,
    x ∈ modelT → x ^ 2 = 1 → x ∉ modelE → x ∉ modelF →
    (commutingSquares x).card = 12 := by decide +kernel

/-- Janko's Lemma 1: the coordinate Sylow subgroup has precisely the two
published elementary subgroups of order sixteen. -/
public theorem model_elementary_sixteen (A : Subgroup TwistedModel)
    (hAT : A ≤ modelT) (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) :
    A = modelE ∨ A = modelF := by
  classical
  let := hA
  have hsub : (A : Set TwistedModel) ⊆ (modelE : Set TwistedModel) ∪ modelF := by
    intro x hx
    by_contra! hn
    let f : A → {y // y ∈ commutingSquares x} := fun y => ⟨y, by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hAT y.property,
        elemPow_eq_one_of_isElementaryAbelian (p := 2) (y : TwistedModel) y.property,
        setLike_mul_comm y.property hx⟩⟩
    have hf : Function.Injective f := by
      intro y w h
      exact Subtype.ext (congrArg (fun t : {y // y ∈ commutingSquares x} => (t : TwistedModel)) h)
    have hle := Nat.card_le_card_of_injective f hf
    have hnE : x ∉ modelE := fun h => hn (Or.inl h)
    have hnF : x ∉ modelF := fun h => hn (Or.inr h)
    have hcount : Nat.card {y // y ∈ commutingSquares x} = 12 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact commutingSquares_card x (hAT hx)
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx) hnE hnF
    rw [hcard, hcount] at hle
    omega
  rcases SubgroupClass.subset_union.mp hsub with h | h
  · exact Or.inl (eq_of_le_of_card_ge h (by rw [hcard, modelE_card]))
  · exact Or.inr (eq_of_le_of_card_ge h (by rw [hcard, modelF_card]))

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
