module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.SourceBounds

/-!
# Parameter assembly for the odd linear cases of K.2

The rank-one source domain is PSL₂(p^e), p odd prime and e in {1,2};
the rank-two domain is PSL₃(p). A coarse bound p^e ≤ 25 leaves only
11, 13, 17, 19, 23 and 25 in addition to the source coincidences.
The arithmetic below gives the exact prime/exponent pairs, and transports
the original central-quotient model to its corresponding surviving parameter.

The assembly is conditional on three independent source calculations:
the coarse rank-one bound, the six small rank-one exclusions, and the
PSL₃ exclusion. It is not the unconditional K.2 theorem. In particular the
threshold is two throughout; a full-normalizer FF exclusion does not supply
any of these premises. Final discharge remains with this module's owner.

Source: Aschbacher--Smith K.2, printed p.453; Guralnick--Malle,
Classification of 2F-modules I, Propositions 4.1--4.2, manuscript pp.8--10.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

/-- The exact finite list after the source's coarse bound q ≤ 25. -/
theorem prime_power_candidates_le_twentyFive {p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : e = 1 ∨ e = 2) (hlo : 4 ≤ p ^ e) (hhi : p ^ e ≤ 25) :
    ((p = 5 ∧ e = 1) ∨ (p = 7 ∧ e = 1) ∨ (p = 3 ∧ e = 2)) ∨
      (p ^ e = 11 ∨ p ^ e = 13 ∨ p ^ e = 17 ∨ p ^ e = 19 ∨
        p ^ e = 23 ∨ p ^ e = 25) := by
  rcases he with rfl | rfl
  · simp only [pow_one] at hlo hhi ⊢
    interval_cases p <;> norm_num at *
  · have hp5 : p ≤ 5 := by nlinarith [hp.two_le]
    interval_cases p <;> norm_num at *

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Assemble the exact source parameters after the three indicated calculations.
Each calculation concerns this same actor, representation and central quotient. -/
theorem linear_parameters_of_source_calculations
    (hsize : ∀ p e : ℕ, p.Prime → Odd p → (e = 1 ∨ e = 2) → 4 ≤ p ^ e →
      ClassicalGroup.IsPSL
        ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 (p ^ e) →
      cubicRatio ρ ≤ 2 → p ^ e ≤ 25)
    (hsmall : ∀ q : ℕ, (q = 11 ∨ q = 13 ∨ q = 17 ∨ q = 19 ∨ q = 23 ∨ q = 25) →
      ClassicalGroup.IsPSL
        ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 q →
      2 < cubicRatio ρ)
    (hthree : ∀ p : ℕ, p.Prime → Odd p →
      ClassicalGroup.IsPSL
        ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 p →
      2 < cubicRatio ρ)
    {n p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcase : (n = 2 ∧ (e = 1 ∨ e = 2) ∧ 4 ≤ p ^ e) ∨ (n = 3 ∧ e = 1))
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) n (p ^ e))
    (hq : cubicRatio ρ ≤ 2) :
    n = 2 ∧ ((p = 5 ∧ e = 1) ∨ (p = 7 ∧ e = 1) ∨ (p = 3 ∧ e = 2)) := by
  rcases hcase with ⟨rfl, he, hlo⟩ | ⟨rfl, rfl⟩
  · refine ⟨rfl, ?_⟩
    rcases prime_power_candidates_le_twentyFive hp ho he hlo
      (hsize p e hp ho he hlo hm hq) with hgood | hbad
    · exact hgood
    · exact (not_lt_of_ge hq (hsmall (p ^ e) hbad hm)).elim
  · exact (not_lt_of_ge hq (hthree p hp ho (by simpa only [pow_one] using hm))).elim

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion
