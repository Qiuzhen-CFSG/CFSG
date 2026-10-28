module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Defs
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Outer.RootPair
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.MaximalExtension
public import Theory.SpecificGroups.SU3.OddInvolutionNormalization
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Normalization and transport for outer five-conjugate generation

The root-and-torus calculation proves four-conjugate generation for entrywise
Hermitian conjugation on the antidiagonal model, and padding proves
`EntrywiseOuterFive`. Odd-prime normalization transports an arbitrary outer
involution to that actor, and the actual multiplicative equivalence transports
the five inner conjugators back. Thus `outerFiveBound` has no outstanding
model-generation premise.

Source: Guralnick--Malle, *Classification of 2F-modules I*, §2 and
Proposition 4.3, and Guralnick--Saxl, *Generation of finite almost simple
groups by conjugates*.  Normalization follows GLS3 §§2.5, 2.7 and 4.3 as
formalized in `OddInvolutionNormalization`.
-/

open Matrix Subgroup
@[expose] public section
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage

universe w

/-- The concrete normalized outer generation obligation.

This records the actual entrywise actor and requires all five conjugators to
come from the projective special unitary group.  It is the sole model input to
`outerFiveBound_of_entrywise`.
-/
def EntrywiseOuterFive : Prop :=
  ∀ {E : Type w} [Field E] [Finite E]
    (J : HermitianForm 3 E)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)] {p : ℕ},
    p.Prime → Odd p → 5 < p → Nat.card E = p ^ 2 →
    (∀ x, J.conj x = x ^ p) →
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) →
    MulAut.HasInnerConjugateCover
      (OddPrimeSylow.NormalizedOuter.entrywiseProjectiveAut J hJ) 5

/-- The concrete entrywise actor has five inner conjugators, by padding the
four-conjugate root-and-torus construction. -/
theorem entrywiseOuterFive : EntrywiseOuterFive.{w} := by
  intro E _ _ J _ p hp _ hp5 hcard hc hJ
  exact (Outer.entrywise_four_cover J hJ hp hp5 hcard hc).mono (by decide)

/-- Odd-prime normalization reduces the outer bound to the antidiagonal model.

The fixed-field cardinality is derived from the quadratic Frobenius data.  The
entrywise actor is identified by the representative-level uniqueness theorem,
then `HasInnerConjugateCover.congr` transports the literal PSU conjugators
through the equivalence supplied by normalization.
-/
theorem outerFiveBound_of_entrywise
    (hmodel : EntrywiseOuterFive.{w}) : OuterFiveBound.{w} := by
  intro E _ _ J _ p hp ho hp5 hcard hc a ha ha2 houter
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype E := Fintype.ofFinite E
  let : CharP E p := charP_of_card_eq_prime_pow (f := 2) (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  have hfixed : Nat.card {x : E // J.conj x = x} = p := by
    have hcard' : Nat.card E = (p ^ 1) ^ 2 := by
      simpa only [pow_one] using hcard
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        hcard' (by simpa only [pow_one] using hc)
  obtain ⟨J₀, e, hconj, hform, hentry⟩ :=
    OddInvolutionNormalization.normalized_outer J hp ho hcard hfixed a ha2 houter
  let _ : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) := e.symm.isSimpleGroup
  have hc₀ : ∀ x, J₀.conj x = x ^ p := by
    rw [hconj]
    exact hc
  have hg : MulAut.congr e a =
      OddPrimeSylow.NormalizedOuter.entrywiseProjectiveAut J₀ hform :=
    (BenderSuzuki.MatrixGroups.HermitianForm.IsEntrywiseConjugation.unique
      (J := J₀) hentry
      (OddPrimeSylow.NormalizedOuter.entrywiseProjectiveAut_isEntrywiseConjugation
        J₀ hform))
  unfold EntrywiseOuterFive at hmodel
  have hb := @hmodel E _ _ J₀ _ p hp ho hp5 hcard hc₀ hform
  rw [← hg] at hb
  have hh := hb.congr e.symm
  have he : MulAut.congr e.symm (MulAut.congr e a) = a := by
    ext x
    simp [MulAut.congr]
  rwa [he] at hh

/-- Every outer involution of PSU₃(p), p > 5, is covered by five conjugates
by actual elements of PSU₃(p). The normalized model input is fully discharged. -/
theorem outerFiveBound : OuterFiveBound.{w} :=
  outerFiveBound_of_entrywise entrywiseOuterFive

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds
