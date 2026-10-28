module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.Candidates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits.Coordinates
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# An intrinsic matrix invariant separating the exceptional kernel subgroups

Simultaneous conjugation preserves the rank of `(u - 1)(v - 1)` in the
literal binary representation. Thus a rank condition quantified over every
member of a subgroup is preserved by its full ambient normalizer. The
finite certificate below would identify its rank-small elements with the
specified four-group, giving the required invariant proper subgroup of the
sixteen-group. The rank certificate itself remains a separate obligation.

The proper nonzero inclusion is proved directly from the original XOR kernel
coordinates, independently of the all-2A catalogue or its proposed orders.
Source context: Aschbacher--Smith A.3.12, printed pp.47--48, and
Kleidman--Wilson (1988), pp.484--510. The imported coordinates retain the
original ATLAS max1 words and embedding.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders
open Subgroup Janko4 Janko4.Cardinality
open Janko4.Cardinality.QuotientCount.Image
open Janko4.Simplicity.Max1Fusion.KernelOrbits
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel

namespace PureNormalizers

lemma maskElement_zero : maskElement 0 = 1 := by
  change ((maskValue matrixA_mul_self matrixB_pow_four 0 :
    max1Subgroup matrixA_mul_self matrixB_pow_four) : Model) = 1
  rw [maskValue_zero]
  rfl

lemma maskElement_xor (m n : ℕ) :
    maskElement (Nat.xor m n) = maskElement m * maskElement n := by
  exact congrArg (fun u : localKernel matrixA_mul_self matrixB_pow_four =>
    ((u : max1Subgroup matrixA_mul_self matrixB_pow_four) : Model))
    (maskValue_xor matrixA_mul_self matrixB_pow_four m n)

/-- An explicit enumeration of the four elements, in the original mask convention. -/
def fourMask (i : Fin 4) : ℕ := ![0, 1387, 198, 1453] i

private def xorIndex (i j : Fin 4) : Fin 4 :=
  ⟨(i.val ^^^ j.val) % 4, Nat.mod_lt _ (by decide)⟩

private lemma fourMask_xor : ∀ i j, fourMask (xorIndex i j) =
    Nat.xor (fourMask i) (fourMask j) := by decide +kernel

/-- The four actual kernel words form a subgroup; no order assertion is assumed. -/
def fourRange : Subgroup Model where
  carrier := Set.range (fun i : Fin 4 => maskElement (fourMask i))
  one_mem' := ⟨0, maskElement_zero⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨xorIndex i j, by
      change maskElement (fourMask (xorIndex i j)) = _
      rw [fourMask_xor, maskElement_xor]⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    refine ⟨i, eq_inv_of_mul_eq_one_left ?_⟩
    rw [← maskElement_xor]
    change maskElement (fourMask i ^^^ fourMask i) = 1
    rw [Nat.xor_self, maskElement_zero]

lemma maskElement_mem_candidate {i : Fin 6} {m : ℕ} (hm : m ∈ candidateRows i) :
    maskElement m ∈ candidate i := subset_closure ⟨m, hm, rfl⟩

lemma candidate_two_eq_fourRange : candidate 2 = fourRange := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨m, hm, rfl⟩
    have hm' : m = 1387 ∨ m = 198 := by simpa [candidateRows] using hm
    rcases hm' with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · have h1 : maskElement 1387 ∈ candidate 2 :=
      maskElement_mem_candidate (by simp [candidateRows])
    have h2 : maskElement 198 ∈ candidate 2 :=
      maskElement_mem_candidate (by simp [candidateRows])
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · change maskElement 0 ∈ candidate 2
      rw [maskElement_zero]
      exact (candidate 2).one_mem
    · exact h1
    · exact h2
    · change maskElement (Nat.xor 1387 198) ∈ candidate 2
      rw [maskElement_xor]
      exact (candidate 2).mul_mem h1 h2

lemma mask_bits_eq_of_eq {m n : ℕ} (h : maskElement m = maskElement n) :
    (fun i : Fin 11 => m.testBit i.val) = (fun i : Fin 11 => n.testBit i.val) :=
  coordinates_injective matrixA_mul_self matrixB_pow_four (Subtype.ext (Subtype.ext h))

lemma fourMask_injective : Function.Injective (fun i => maskElement (fourMask i)) := by
  intro i j h
  have he := mask_bits_eq_of_eq h
  have hinj : Function.Injective (fun i : Fin 4 =>
    (fun k : Fin 11 => (fourMask i).testBit k.val)) := by decide +kernel
  exact hinj he

/-- This count uses the literal four words and injective kernel coordinates. -/
theorem candidate_two_card : Nat.card (candidate 2) = 4 := by
  rw [candidate_two_eq_fourRange]
  let f : Fin 4 → fourRange := fun i => ⟨maskElement (fourMask i), ⟨i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact fourMask_injective (congrArg (fun z : fourRange => (z : Model)) h)
    · rintro ⟨g, ⟨i, rfl⟩⟩
      exact ⟨i, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf).symm).trans (Nat.card_fin 4)

theorem candidate_two_ne_bot : candidate 2 ≠ ⊥ := by
  intro h
  have hc := candidate_two_card
  rw [h, card_bot] at hc
  omega

lemma candidate_two_le_five : candidate 2 ≤ candidate 5 := by
  apply (closure_le _).mpr
  rintro _ ⟨m, hm, rfl⟩
  have hm' : m = 1387 ∨ m = 198 := by simpa [candidateRows] using hm
  rcases hm' with rfl | rfl
  · change maskElement (Nat.xor 1049 370) ∈ candidate 5
    rw [maskElement_xor]
    exact (candidate 5).mul_mem
      (maskElement_mem_candidate (by simp [candidateRows]))
      (maskElement_mem_candidate (by simp [candidateRows]))
  · exact maskElement_mem_candidate (by simp [candidateRows])

/-- The actual four-group is a strict subgroup of the proposed sixteen-group. -/
theorem candidate_two_lt_five : candidate 2 < candidate 5 := by
  refine lt_of_le_not_ge candidate_two_le_five ?_
  intro h
  have hm : maskElement 1049 ∈ candidate 2 :=
    h (maskElement_mem_candidate (by simp [candidateRows]))
  rw [candidate_two_eq_fourRange] at hm
  obtain ⟨i, hi⟩ := hm
  have hne : ∀ i : Fin 4, (fun k : Fin 11 => (fourMask i).testBit k.val) ≠
      (fun k : Fin 11 => (1049 : ℕ).testBit k.val) := by decide +kernel
  exact hne i (mask_bits_eq_of_eq hi)

/-- The rank of the product of the two displacement matrices. -/
noncomputable def pairRank (u v : Model) : ℕ :=
  ((toMatrix u - 1) * (toMatrix v - 1)).rank

private lemma displacement_conj (g u : Model) :
    toMatrix (g * u * g⁻¹) - 1 = toMatrix g * (toMatrix u - 1) * toMatrix g⁻¹ := by
  simp only [sub_mul, mul_sub, mul_one, ← map_mul,
    mul_inv_cancel, map_one]

private lemma displacement_product_conj (g u v : Model) :
    (toMatrix (g * u * g⁻¹) - 1) * (toMatrix (g * v * g⁻¹) - 1) =
    toMatrix g * ((toMatrix u - 1) * (toMatrix v - 1)) * toMatrix g⁻¹ := by
  rw [displacement_conj, displacement_conj]
  have hi : toMatrix g⁻¹ * toMatrix g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  simp only [mul_assoc, ← mul_assoc (toMatrix g⁻¹), hi, one_mul]

private lemma pairRank_conj_le (g u v : Model) :
    pairRank (g * u * g⁻¹) (g * v * g⁻¹) ≤ pairRank u v := by
  unfold pairRank
  rw [displacement_product_conj]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- Rank is invariant under simultaneous conjugation in the FULL ambient model. -/
theorem pairRank_conj (g u v : Model) :
    pairRank (g * u * g⁻¹) (g * v * g⁻¹) = pairRank u v := by
  refine le_antisymm (pairRank_conj_le g u v) ?_
  have h := pairRank_conj_le g⁻¹ (g * u * g⁻¹) (g * v * g⁻¹)
  simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h

/-- A finite matrix certificate. It contains no normalizer hypothesis or conclusion.
The predicted ranks are 0, 16 and 20; the threshold distinguishes the four-group. -/
def SmallPairRanks : Prop :=
  ∀ u ∈ candidate 5,
    (∀ v ∈ candidate 5, pairRank u v ≤ 16) ↔ u ∈ candidate 2

/-- The finite rank certificate gives invariance under every ambient normalizer element. -/
theorem normalizer_five_le_two_of_pair_ranks (hrank : SmallPairRanks) :
    normalizer (candidate 5 : Set Model) ≤ normalizer (candidate 2 : Set Model) := by
  apply le_normalizer_iff.mpr
  intro g hg u hu
  have hu5 := candidate_two_le_five hu
  have hgu := (mem_normalizer_iff.mp hg u).mp hu5
  apply (hrank _ hgu).mp
  intro v hv
  have hv' : g⁻¹ * v * g ∈ candidate 5 := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((normalizer (candidate 5 : Set Model)).inv_mem hg) v).mp hv
  have h := (hrank u hu5).mpr hu (g⁻¹ * v * g) hv'
  have he := pairRank_conj g u (g⁻¹ * v * g)
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at he
  calc
    _ = pairRank u (g⁻¹ * v * g) := by simpa only [mul_assoc] using he
    _ ≤ 16 := h

/-- Actual application to the second exceptional index, with a literal invariant subgroup. -/
theorem candidate_five_obstruction_of_pair_ranks (hrank : SmallPairRanks) :
    ∃ B : Subgroup Model, B < candidate (exceptionalIndex 1) ∧ B ≠ ⊥ ∧
      normalizer (candidate (exceptionalIndex 1) : Set Model) ≤ normalizer (B : Set Model) :=
  ⟨candidate 2, candidate_two_lt_five, candidate_two_ne_bot,
    normalizer_five_le_two_of_pair_ranks hrank⟩

end PureNormalizers
end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders
