module
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Structure
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Context
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.NormalizerControl.Geometry
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The intrinsic order-sixteen subgroup of Q

The elementary subgroup F is characterized by having at least sixteen
commuting involutions in Q, identity included. An explicit list of all 28
involutions makes the finite centralizer count small. Cardinality invariance
then proves that every automorphism of Q preserves F.

These are local ingredients for the independent normalizer argument toward
Huppert--Blackburn III, XII.1.18(b), printed p.314.
-/
namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl.ExceptionalAction
open NonsplitModels Model Subgroup
set_option maxRecDepth 100000

private abbrev CI (x : exceptionalSubgroup) :=
  {q : exceptionalSubgroup // q ^ 2 = 1 ∧ q * x = x * q}

private def involutionRows (i : Fin 28) : Second :=
  element (![0, 1, 8, 9, 20, 21, 24, 25, 32, 33, 48, 49, 60, 61,
    96, 97, 108, 109, 116, 117, 180, 181, 188, 189, 244, 245, 256, 257] i)

private theorem involutionRows_mem : ∀ i,
    involutionRows i ∈ exceptionalSubgroup ∧ (involutionRows i) ^ 2 = 1 := by
  decide +kernel

private theorem involutionRows_injective : Function.Injective involutionRows := by
  exact (by decide +kernel : ∀ i j, involutionRows i = involutionRows j → i = j)

private theorem involutionRows_cover (q : exceptionalSubgroup) (hq : q ^ 2 = 1) :
    ∃ i, involutionRows i = (q : Second) := by
  obtain ⟨j, hj⟩ := element_bijective.2 (q : Second)
  have h := (by decide +kernel : ∀ j : Fin 384,
    element j ∈ exceptionalSubgroup → (element j) ^ 2 = 1 →
    ∃ i, involutionRows i = element j) j
  rw [hj] at h
  exact h q.property (congrArg Subtype.val hq)

private theorem CI_card (x : exceptionalSubgroup) : Nat.card (CI x) =
    Fintype.card {i : Fin 28 // involutionRows i * (x : Second) = x * involutionRows i} := by
  let f : {i : Fin 28 // involutionRows i * (x : Second) = x * involutionRows i} → CI x :=
    fun i => ⟨⟨involutionRows i, (involutionRows_mem i).1⟩,
      Subtype.ext (involutionRows_mem i).2, Subtype.ext i.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact Subtype.ext (involutionRows_injective
        (congrArg (fun q : CI x => (q.val : Second)) h))
    · rintro ⟨q, hs, hc⟩
      obtain ⟨i, hi⟩ := involutionRows_cover q hs
      refine ⟨⟨i, ?_⟩, ?_⟩
      · simpa only [hi, Subgroup.coe_mul] using congrArg Subtype.val hc
      · exact Subtype.ext (Subtype.ext hi)
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

private theorem small_rows : ∀ i : Fin 384,
    element i ∈ exceptionalSubgroup → element i ∉ fourGroup → (element i) ^ 2 = 1 →
    Fintype.card {j : Fin 28 // involutionRows j * element i = element i * involutionRows j}
      < 16 := by decide +kernel

private theorem four_intrinsic (x : exceptionalSubgroup) :
    (x : Second) ∈ fourGroup ↔ x ^ 2 = 1 ∧ 16 ≤ Nat.card (CI x) := by
  constructor
  · intro hx
    have hs : x ^ 2 = 1 := Subtype.ext (fourGroup_square x hx)
    refine ⟨hs, ?_⟩
    let f : fourGroup → CI x := fun y =>
      ⟨⟨y, fourGroup_le_exceptionalSubgroup y.property⟩,
        Subtype.ext (fourGroup_square y y.property),
        Subtype.ext (fourGroup_comm y x y.property hx)⟩
    have hf : Function.Injective f := by
      intro a b h
      exact Subtype.ext (congrArg (fun t : CI x => (t.val : Second)) h)
    simpa only [fourGroup_card] using Nat.card_le_card_of_injective f hf
  · rintro ⟨hs, hc⟩
    by_contra hn
    obtain ⟨i, hi⟩ := element_bijective.2 (x : Second)
    have hh := small_rows i (hi ▸ x.property) (hi ▸ hn)
      (by simpa only [hi, Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hs)
    rw [hi, ← CI_card x] at hh
    omega

/-- Every automorphism of Q preserves its distinguished elementary subgroup F. -/
public theorem four_invariant (a : MulAut exceptionalSubgroup) (x : exceptionalSubgroup) :
    (a x : Second) ∈ fourGroup ↔ (x : Second) ∈ fourGroup := by
  have hc : Nat.card (CI x) = Nat.card (CI (a x)) := by
    apply Nat.card_congr
    exact a.toEquiv.subtypeEquiv (by
      intro q
      change (q ^ 2 = 1 ∧ q * x = x * q) ↔
        ((a q) ^ 2 = 1 ∧ a q * a x = a x * a q)
      simp only [← map_pow, a.map_eq_one_iff, ← map_mul, a.injective.eq_iff])
  rw [four_intrinsic, four_intrinsic, ← hc]
  simp only [← map_pow, a.map_eq_one_iff]

end Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl.ExceptionalAction
