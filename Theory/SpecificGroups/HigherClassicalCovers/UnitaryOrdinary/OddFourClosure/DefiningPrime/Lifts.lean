module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime.Roots
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime.Collection
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime.Lifts.Preimages
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Preparation for positive-root lifts in defining-prime SU₄ covers

The full preimages of all four positive root groups are abelian in a cover
with kernel of order q > 3. For the two short roots this follows from the
actual doubling torus and its action on the central commutator. For the two
long roots it follows from the prime cardinality of the trace-zero group.
The theorem below applies those calculations to the literal covering map.

Constructing `EquivariantRootLifts` and deriving the six cross-root relations
remain separate obligations. Thus this preparation does not yet prove
`positiveRootLifts_of_prime_kernel` or assert a section of the positive group.
The final assembly belongs in this module.

Source: GLS3 §6.1 and Aschbacher--Smith I.1.4(3), printed p.408.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 4 F)

/-- The four abelian-preimage inputs for the actual prime-degree cover.
No Mersenne or quasisimplicity hypothesis is needed for this local step. -/
theorem prime_cover_root_preimages_commute {q : ℕ} (hp : q.Prime) (hq : 3 < q)
    (hcard : Nat.card F = q^2) (hconj : ∀ x, J.conj x = x^q)
    {E : Type*} [Group E] (f : PerfectCentralCovering.Cover E (HyperbolicSU J))
    (hdegree : Nat.card f.toMonoidHom.ker = q) :
    (∀ x y : E, f.toMonoidHom x ∈ (shortRoot J).range →
      f.toMonoidHom y ∈ (shortRoot J).range → Commute x y) ∧
    (∀ x y : E, f.toMonoidHom x ∈ (highRoot J).range →
      f.toMonoidHom y ∈ (highRoot J).range → Commute x y) ∧
    (∀ x y : E, f.toMonoidHom x ∈ (middleRoot J).range →
      f.toMonoidHom y ∈ (middleRoot J).range → Commute x y) ∧
    (∀ x y : E, f.toMonoidHom x ∈ (longRoot J).range →
      f.toMonoidHom y ∈ (longRoot J).range → Commute x y) := by
  exact ⟨fun _ _ => short_preimage_commute_of_prime_kernel J f.toMonoidHom
      f.surjective f.ker_le_center hp hq hcard hdegree,
    fun _ _ => high_preimage_commute J f.toMonoidHom
      f.surjective f.ker_le_center hp hcard hconj,
    fun _ _ => middle_preimage_commute_of_prime_kernel J f.toMonoidHom
      f.surjective f.ker_le_center hp hq hcard hdegree,
    fun _ _ => long_preimage_commute J f.toMonoidHom
      f.surjective f.ker_le_center hp hcard hconj⟩

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime
