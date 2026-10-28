module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Representatives

/-!
# Lifting the max2 quotient and fiber census

A quotient conjugator lifts to the literal group H. Conjugating an element
with square one into one of four quotient fibers and using the exhaustive
8192 kernel coordinates reduces its local class to the finite fiber problem.
Neither quotient coverage nor the finite fiber census is assumed to be proved
here: they are explicit independent certificate inputs.

Source motivation: Aschbacher--Smith, `refs/quasithin.pdf`, pp.64--65, A.6.1--4.
-/

public section
namespace Janko4.Cardinality.LocalInvolutionCensus
open Coordinates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound

/-- Quotient coverage and the finite lift equations give coverage inside H. -/
theorem square_one_coverage_of_quotient_and_fibers
    (hH : Nat.card H ≤ 21799895040)
    (hquotient : ∀ v : Q, v ^ 2 = 1 → ∃ j : Fin 4, IsConj (q (lift j)) v)
    (hfibers : ∀ (j : Fin 4) (i : Fin 8192),
      (localKernelProduct i * lift j) ^ 2 = 1 →
        ∃ k : Fin 11, IsConj (representative k) (localKernelProduct i * lift j))
    (u : H) (hu : u ^ 2 = 1) :
    ∃ k : Fin 11, IsConj (representative k) u := by
  have hqu : (q u) ^ 2 = 1 := by rw [← map_pow, hu, map_one]
  obtain ⟨j, hj⟩ := hquotient (q u) hqu
  obtain ⟨v, hv⟩ := isConj_iff.mp hj.symm
  obtain ⟨g, rfl⟩ := q_surjective v
  let u' := g * u * g⁻¹
  have he : q u' = q (lift j) := by
    simpa only [u', map_mul, map_inv] using hv
  have he' : localQuotientMap u' = localQuotientMap (lift j) := by
    simpa only [coe_q] using congrArg (fun v : Q => (v : QuotientMatrixˣ)) he
  obtain ⟨i, hi⟩ := local_fiber hH u' (lift j) he'
  have hu' : u' ^ 2 = 1 := by
    change (MulAut.conj g u) ^ 2 = 1
    rw [← map_pow, hu, map_one]
  obtain ⟨k, hk⟩ := hfibers j i (hi ▸ hu')
  refine ⟨k, ?_⟩
  have hc : IsConj u u' := isConj_iff.mpr ⟨g, rfl⟩
  rw [← hi] at hk
  exact hk.trans hc.symm

end Janko4.Cardinality.LocalInvolutionCensus
