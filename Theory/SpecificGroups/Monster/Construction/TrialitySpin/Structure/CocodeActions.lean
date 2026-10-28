module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.SignKernel

/-!
# Cocode actions and the associator functional

The standard projection has precisely the previously specified
`IsSignAutomorphism` permutations as kernel. Perfect cocode duality makes each
such permutation the sign action of a unique cocode word. The cocode class of
the pointwise product of two Golay words induces their triple-intersection
functional. Its action on the loop is the associator automorphism, and it is
even because Golay words are pairwise orthogonal.

Source: Aschbacher, *Sporadic Groups*, Remark 14.1, p. 58, and Lemma 27.1,
p. 144. Here pointwise multiplication is intersection of binary supports.
-/

@[expose] public section

open Atlas.Fischer Atlas.Codes
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin

theorem parkerStandardProjection_eq_one_iff (e : ParkerStandardGroup) :
    parkerStandardProjection e = 1 ↔ IsSignAutomorphism e.val := by
  constructor
  · intro he
    refine ⟨e.prop, ?_⟩
    intro x
    rw [parkerStandardProjection_spec, he, parkerCodeEquiv_one]
  · intro he
    apply parkerCodeEquiv_faithful
    intro a
    exact (parkerStandardProjection_spec e (a,0)).symm.trans
      ((he.2 (a,0)).trans (parkerCodeEquiv_one a).symm)

theorem isSignAutomorphism_iff_cocode (e : Equiv.Perm ParkerLoop) :
    IsSignAutomorphism e ↔ ∃ c : Cocode, (parkerCocodeStandard c).val = e := by
  constructor
  · intro he
    let a : ParkerStandardGroup := ⟨e,he.1⟩
    have ha : parkerStandardProjection a = 1 :=
      (parkerStandardProjection_eq_one_iff a).mpr he
    obtain ⟨c,hc⟩ := parkerCocodeKernelHom_surjective ⟨a,ha⟩
    exact ⟨c.toAdd, congrArg (fun x : parkerStandardProjection.ker => x.val.val) hc⟩
  · rintro ⟨c,rfl⟩
    exact (parkerStandardProjection_eq_one_iff _).mp (parkerCocodeStandard_projection c)

/-- Cocode representative of the intersection of two Golay supports. -/
def intersectionCocode (a b : golay) : Cocode :=
  Submodule.Quotient.mk (fun p => a.val p * b.val p : BinaryWord)

/-- The associator functional of Remark 14.1, via the actual cocode pairing. -/
def associatorFunctional (a b : golay) : Module.Dual Bit golay :=
  cocodeDualEquiv (intersectionCocode a b)

theorem associatorFunctional_apply (a b c : golay) :
    associatorFunctional a b c = parkerTripleIntersection a b c := by
  rw [associatorFunctional, intersectionCocode, cocodeDualEquiv_mk]
  simp only [binaryDot_apply, parkerTripleIntersection]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- The actual standard automorphism `α_(a,b)` from Remark 14.1. -/
def associatorAutomorphism (a b : golay) : ParkerStandardGroup :=
  parkerCocodeStandard (intersectionCocode a b)

theorem associatorAutomorphism_apply (a b : golay) (x : ParkerLoop) :
    (associatorAutomorphism a b).val x = parkerSign (parkerTripleIntersection a b x.1) x := by
  rw [associatorAutomorphism, parkerCocodeStandard_apply]
  change (x.1,x.2+associatorFunctional a b x.1) = _
  rw [associatorFunctional_apply]
  rfl

theorem associatorAutomorphism_even (a b : golay) :
    (associatorAutomorphism a b).val parkerOmega = parkerOmega := by
  rw [associatorAutomorphism_apply]
  change parkerSign (parkerTripleIntersection a b golayOne) parkerOmega = parkerOmega
  rw [parkerTripleIntersection_cycle, parkerTripleIntersection_one, parkerSign_zero]

end Sporadic.Monster.Construction.TrialitySpin
