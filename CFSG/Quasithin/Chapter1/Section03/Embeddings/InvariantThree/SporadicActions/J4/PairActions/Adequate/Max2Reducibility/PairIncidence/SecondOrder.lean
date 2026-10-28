module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.MatrixConditions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.SylowCover.Orbit
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Second

/-!
# A nine-point bound for the actual second matrix candidate

The three words defining `involutionMatrixSecondSubgroup` preserve nine
unordered binary row pairs. Their existing matrix certificates and the
kernel-checked transition table below prove preservation, including inverses.
Explicit words reach all nine displayed pairs from the seed.

The 10395 distinct reachable pair images in `SylowCover.Orbit`, together with
ambient order 2661120, bound the full seed fixer by 256. Factoring candidate
elements through the nine representatives and that fixer gives order at most
2304, hence excludes divisibility by 6912. No candidate-placement or
three-core hypothesis enters this argument.

Witness provenance: `source/candidate_witnesses.py` and its JSON output are
untrusted discovery data; all matrix transitions are proved here. Source
context: Aschbacher–Smith, Proposition 1.3.4, printed p.511/PDF p.528 of
`refs/quasithin.pdf`, and GLS3 Table 5.3i. This is the finite order calculation
for the second candidate, not the whole source proposition.
-/

open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound LowerBound.QuotientOrderCertificate
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2.SecondOrder
open FiniteIncidence FiniteIncidence.SylowCover FiniteIncidence.ObstructionCertificate
attribute [local irreducible] Janko4.modelGroup quotientSubgroup baseSubgroup

private theorem pairRight_injective (g : A) : Function.Injective (fun p => pairRight p g) := by
  intro p q h
  have h' := congrArg (fun r => pairRight r g⁻¹) h
  simpa only [← pairRight_mul, mul_inv_cancel, pairRight_one] using h'

private theorem fixer_card_le : Nat.card fixer ≤ 256 := by
  classical
  choose j b hb hpoint using Orbit.reachable
  let rep : Fin 10395 → A := fun i => representative (j i) * b i
  have hi : Function.Injective (fun i => pairRight seed (rep i)) := by
    intro i k h
    apply Orbit.distinct
    simpa only [rep, hpoint] using h
  let f : Fin 10395 × fixer → A := fun p => p.2.val * rep p.1
  have hf : Function.Injective f := by
    rintro ⟨i,a⟩ ⟨k,b⟩ h
    have hik : i = k := by
      apply hi
      have hv := congrArg (pairRight seed) h
      change pairRight seed (a.val * rep i) = pairRight seed (b.val * rep k) at hv
      simpa only [pairRight_mul, show pairRight seed a.val = seed from a.property,
        show pairRight seed b.val = seed from b.property] using hv
    subst k
    have hab : a = b := Subtype.ext (mul_right_cancel h)
    subst b
    rfl
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_fin, involutionMatrixQuotient_card] at hc
  omega

private def codes : Fin 9 → Code :=
  ![(2148, 2163), (666, 1047), (1024, 2814), (1047, 1677), (2814, 3838),
    (1024, 3838), (23, 2163), (666, 1677), (23, 2148)]

private def transition : Fin 3 → Fin 9 → Fin 9 :=
  ![![1, 0, 4, 6, 2, 5, 3, 8, 7],
    ![0, 2, 1, 5, 7, 3, 6, 4, 8],
    ![0, 3, 5, 1, 4, 2, 8, 7, 6]]

private def rows : Fin 3 → Vector ℕ 12 :=
  ![#v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605],
    #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100],
    #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184]]

private theorem generator_value (t : Fin 3) :
    (involutionMatrixSecondGenerator t).val.val = quotientDecode (rows t) := by
  fin_cases t
  · exact e0_value
  · exact e1_value
  · exact e2_value

private theorem checked : ∀ t i, Step (codes i) (codes (transition t i)) (rows t) := by
  decide +kernel

private theorem transition_twice : ∀ t i, transition t (transition t i) = i := by
  decide +kernel

private theorem generator_step (t : Fin 3) (i : Fin 9) :
    pairRight (point (codes i)) (involutionMatrixSecondGenerator t) =
      point (codes (transition t i)) :=
  step_sound _ _ _ _ (generator_value t) (checked t i)

private def preserves : Subgroup A where
  carrier := {g | ∀ p, (∃ i, point (codes i) = p) ↔
    ∃ i, point (codes i) = pairRight p g}
  one_mem' := fun p => by rw [pairRight_one]
  mul_mem' := by
    intro a b ha hb p
    rw [pairRight_mul]
    exact (ha p).trans (hb (pairRight p a))
  inv_mem' := by
    intro a ha p
    have h := ha (pairRight p a⁻¹)
    simpa only [← pairRight_mul, inv_mul_cancel, pairRight_one] using h.symm

private theorem second_preserves : involutionMatrixSecondSubgroup ≤ preserves := by
  apply (Subgroup.closure_le preserves).mpr
  rintro _ ⟨t, rfl⟩ p
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨transition t i, (generator_step t i).symm⟩
  · rintro ⟨j, hj⟩
    refine ⟨transition t j, pairRight_injective (involutionMatrixSecondGenerator t) ?_⟩
    change pairRight (point (codes (transition t j))) (involutionMatrixSecondGenerator t) = _
    rw [generator_step, transition_twice]
    exact hj

private def words : Fin 9 → List (Fin 3) :=
  ![[], [0], [0, 1], [0, 2], [0, 1, 0], [0, 1, 2], [0, 2, 0],
    [0, 1, 0, 1], [0, 2, 0, 2]]

private def rep (i : Fin 9) : A := (words i |>.map involutionMatrixSecondGenerator).prod

private theorem rep_image (i : Fin 9) : pairRight seed (rep i) = point (codes i) := by
  change pairRight (point (codes 0)) (rep i) = point (codes i)
  fin_cases i <;>
    norm_num [rep, words, pairRight_mul, pairRight_one, generator_step, transition] <;> rfl

private theorem second_card_le : Nat.card involutionMatrixSecondSubgroup ≤ 2304 := by
  classical
  have hcover (x : involutionMatrixSecondSubgroup) :
      ∃ i, point (codes i) = pairRight seed x.val :=
    (second_preserves x.property seed).mp ⟨0, rfl⟩
  choose label hlabel using hcover
  have hfix (x : involutionMatrixSecondSubgroup) :
      x.val * (rep (label x))⁻¹ ∈ fixer := by
    change pairRight seed (x.val * (rep (label x))⁻¹) = seed
    rw [pairRight_mul, ← hlabel x, ← rep_image (label x), ← pairRight_mul,
      mul_inv_cancel, pairRight_one]
  let f : involutionMatrixSecondSubgroup → Fin 9 × fixer :=
    fun x => ⟨label x, ⟨x.val * (rep (label x))⁻¹, hfix x⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    have hi : label x = label y := congrArg Prod.fst h
    have hv : x.val * (rep (label x))⁻¹ = y.val * (rep (label y))⁻¹ :=
      congrArg (fun z => z.2.val) h
    rw [hi] at hv
    exact Subtype.ext (mul_right_cancel hv)
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_fin] at hc
  have hb := fixer_card_le
  omega

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2.SecondOrder

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2

/-- The closure of the three actual second-candidate words has order at most 2304. -/
public theorem second_order_le_2304 : Nat.card involutionMatrixSecondSubgroup ≤ 2304 :=
  SecondOrder.second_card_le

/-- An order-6912 subgroup cannot be contained in the second matrix candidate. -/
public theorem second_order_not_divisible_6912 :
    ¬ 6912 ∣ Nat.card involutionMatrixSecondSubgroup := by
  intro hd
  have h := Nat.le_of_dvd (Nat.card_pos (α := involutionMatrixSecondSubgroup)) hd
  have hb := second_order_le_2304
  omega

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2
