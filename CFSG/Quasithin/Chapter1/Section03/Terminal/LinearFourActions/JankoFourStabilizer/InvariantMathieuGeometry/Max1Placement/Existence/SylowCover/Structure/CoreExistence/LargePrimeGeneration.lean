module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.CoreExistence.Contracts
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Thompson
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.CoreExistence.LargePrimeGeneration.Rank23
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.CoreExistence.LargePrimeGeneration.Rank29
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.CoreExistence.LargePrimeGeneration.Rank31
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.CoreExistence.LargePrimeGeneration.Rank37
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.CoreExistence.LargePrimeGeneration.Rank43
import Mathlib.Algebra.Ring.GeomSum

/-!
# Large-prime exclusion for the marked J₄ Sylow-overgroup argument

The standard involution a has displacement rank 50 in the literal binary
112-dimensional representation. If a inverts r, then r² is the product of two
conjugates of a, and hence has displacement rank at most 100. Each of the
certified words of orders 23, 29, 31, 37 and 43 has displacement rank at least
101, by checked row combinations and identity minors.

Each prime occurs only once in the certified ambient order. Thus every element
of that prime order is conjugate to a power of r² whenever r has that order.
Conjugation preserves displacement rank, and powers cannot increase it. This
rules out the inversion premise for every such r, so the requested generation
contract holds for every Sylow subgroup of the full centralizer. No classification
of simultaneous inverter/Sylow markings is required.

Source context: Aschbacher–Smith A.1.2 and A.3.12, printed pp.47–48, citing
Aschbacher (1986), Memoirs AMS 60, no.343, and Kleidman–Wilson (1988),
pp.484–510. This is an independent matrix proof of the large-prime input
in the Baer–Suzuki route to that Sylow-overgroup step. ATLAS matrices and
word attribution: `Janko4.Model.Data` and `Janko4.Model.Simplicity.Words`.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover

open Janko4 Janko4.Cardinality.LocalInvolutionCensus
open Janko4.Cardinality.LocalInvolutionCensus.FiberCensus
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem a_rank : displacementRank Janko4.a = 50 := by
  have hr := congrArg Prod.fst (FiberCensus.representative_rankPair_of_source
    FiberCensus.sourceRepresentative_rankPair 2)
  change displacementRank (eH (representative 2)) = 50 at hr
  exact (displacementRank_of_isConj
    (firstTarget_isConj_representative 2)).trans hr

private theorem rank_add_le {K n : Type*} [Field K] [Fintype n]
    (A B : Matrix n n K) : (A + B).rank ≤ A.rank + B.rank := by
  change Module.finrank K (LinearMap.range (A + B).mulVecLin) ≤
    Module.finrank K (LinearMap.range A.mulVecLin) +
      Module.finrank K (LinearMap.range B.mulVecLin)
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank
      (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin))

private theorem rank_pow_le (r : Model) (n : ℕ) :
    displacementRank (r ^ n) ≤ displacementRank r := by
  unfold displacementRank
  rw [map_pow, ← geom_sum_mul]
  exact Matrix.rank_mul_le_right _ _

private theorem rank_mul_le (r s : Model) :
    displacementRank (r * s) ≤ displacementRank r + displacementRank s := by
  have he : toMatrix (r * s) - 1 =
      (toMatrix r - 1) * toMatrix s + (toMatrix s - 1) := by
    rw [map_mul, sub_mul, one_mul]
    abel
  unfold displacementRank
  rw [he]
  exact (rank_add_le _ _).trans
    (Nat.add_le_add_right (Matrix.rank_mul_le_left _ _) _)

private theorem rank_square_le (r : Model)
    (h : (MulAut.conj Janko4.a) r = r⁻¹) : displacementRank (r ^ 2) ≤ 100 := by
  have ha : Janko4.a⁻¹ = Janko4.a :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using Janko4.a_pow_two)
  have hi : (MulAut.conj Janko4.a) r⁻¹ = r := by
    rw [map_inv, h, inv_inv]
  change Janko4.a * r⁻¹ * Janko4.a⁻¹ = r at hi
  rw [ha] at hi
  have he : r ^ 2 = (r * Janko4.a * r⁻¹) * Janko4.a := by
    rw [mul_assoc, mul_assoc, ← mul_assoc Janko4.a, hi, pow_two]
  rw [he]
  have hu := rank_mul_le (r * Janko4.a * r⁻¹) Janko4.a
  rw [displacementRank_conj, a_rank] at hu
  exact hu

private theorem no_inversion_of_rank {q : ℕ} (hp : q.Prime) (hodd : q.Coprime 2)
    (hsq : ¬ q ^ 2 ∣ Nat.card Model)
    (x : Model) (hx : orderOf x = q) (hlo : 100 < displacementRank x)
    (r : Model) (hr : orderOf r = q) : (MulAut.conj Janko4.a) r ≠ r⁻¹ := by
  intro hi
  have hr2 : orderOf (r ^ 2) = q := by
    rw [(show (orderOf r).Coprime 2 by rwa [hr]).orderOf_pow, hr]
  obtain ⟨k, g, hg⟩ := Janko4.Simplicity.exists_conjugate_pow_of_prime_sq_not_dvd
    hp hsq hr2 hx
  have hu : displacementRank x ≤ 100 := by
    rw [hg, displacementRank_conj]
    exact (rank_pow_le _ _).trans (rank_square_le r hi)
  omega

open Janko4 Janko4.Simplicity Janko4.Simplicity.WordOrderCertificates
open Janko4.GeneratorCertificates
open Janko4.Cardinality.LocalInvolutionCensus.FiberCensus

private theorem representative_matrix_23 :
    toMatrix (primeRepresentative Janko4.a Janko4.b 7) = decodeRows t4Rows := by
  rw [decode_t4]
  simp [primeRepresentative, word, mul_assoc]

private theorem representative_matrix_29 :
    toMatrix (primeRepresentative Janko4.a Janko4.b 8) = decodeRows t6Rows := by
  rw [decode_t6]
  simp [primeRepresentative, word, mul_assoc]

private theorem representative_matrix_31 :
    toMatrix (primeRepresentative Janko4.a Janko4.b 9) = decodeRows t7Rows := by
  rw [decode_t7]
  simp [primeRepresentative, word, mul_assoc]

private theorem representative_matrix_37 :
    toMatrix (primeRepresentative Janko4.a Janko4.b 10) = decodeRows cRows := by
  rw [decode_c]
  simp [primeRepresentative]

private theorem representative_matrix_43 :
    toMatrix (primeRepresentative Janko4.a Janko4.b 11) = decodeRows t3Rows := by
  rw [decode_t3]
  simp [primeRepresentative, word, mul_assoc]

private theorem large_prime_representative (q : ℕ)
    (hq : q ∈ ({23, 29, 31, 37, 43} : Finset ℕ)) :
    ∃ x : Model, orderOf x = q ∧ 100 < displacementRank x := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · refine ⟨primeRepresentative Janko4.a Janko4.b 7,
      orderOf_primeRepresentative_twentyThree matrixA_mul_self matrixB_pow_four, ?_⟩
    unfold displacementRank
    rw [representative_matrix_23]
    exact LargePrimeRanks.rank_ge_23
  · refine ⟨primeRepresentative Janko4.a Janko4.b 8,
      orderOf_primeRepresentative_twentyNine matrixA_mul_self matrixB_pow_four, ?_⟩
    unfold displacementRank
    rw [representative_matrix_29]
    exact LargePrimeRanks.rank_ge_29
  · refine ⟨primeRepresentative Janko4.a Janko4.b 9,
      orderOf_primeRepresentative_thirtyOne matrixA_mul_self matrixB_pow_four, ?_⟩
    unfold displacementRank
    rw [representative_matrix_31]
    exact LargePrimeRanks.rank_ge_31
  · refine ⟨primeRepresentative Janko4.a Janko4.b 10,
      orderOf_primeRepresentative_thirtySeven matrixA_mul_self matrixB_pow_four, ?_⟩
    unfold displacementRank
    rw [representative_matrix_37]
    exact LargePrimeRanks.rank_ge_37
  · refine ⟨primeRepresentative Janko4.a Janko4.b 11,
      orderOf_primeRepresentative_fortyThree matrixA_mul_self matrixB_pow_four, ?_⟩
    unfold displacementRank
    rw [representative_matrix_43]
    exact LargePrimeRanks.rank_ge_43

/-- The standard central involution inverts no element of any of these five
prime orders. This excludes every element, not only the chosen word witnesses. -/
theorem not_a_inverts_largePrime (q : ℕ)
    (hq : q ∈ ({23, 29, 31, 37, 43} : Finset ℕ))
    (r : Model) (hr : orderOf r = q) : (MulAut.conj Janko4.a) r ≠ r⁻¹ := by
  have ha : q.Prime ∧ q.Coprime 2 ∧ ¬ q ^ 2 ∣ Nat.card Model := by
    rw [Janko4.Cardinality.Thompson.model_card]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨x, hx, hlo⟩ := large_prime_representative q hq
  exact no_inversion_of_rank ha.1 ha.2.1 ha.2.2 x hx hlo r hr

/-- The literal marked large-prime generation contract. The inversion premise
is impossible by the checked displacement ranks, independently of the chosen P. -/
theorem centralLargePrimeGeneration : CentralLargePrimeGeneration := by
  intro P q hq r hr hinv
  exact (not_a_inverts_largePrime q hq r hr hinv).elim

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
