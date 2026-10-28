module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.Inputs
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel.Generators
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.SemilinearReduction
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport

/-!
# The marked concrete S₇ embedding problem

Fix the antidiagonal Hermitian form over GF(25) and its actual entrywise
automorphism. The remaining matrix construction must embed S₇ in its
automorphism group, carry even permutations to inner automorphisms, and
carry `(01)(23)(45)` to the specified entrywise automorphism. This is an
unproved existence predicate. It contains neither maximality nor generation.

Even permutation conjugators from `Generators` then give the literal
PSU₃ conjugators required in Guralnick–Malle, Proposition 4.3, pp.10–11.
-/

@[expose] public noncomputable section
open Equiv Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer
open OddPrimeSylow.NormalizedOuter

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The concrete antidiagonal model, with fifth-power conjugation. -/
abbrev concreteForm := FormTransport.standardForm standardForm

abbrev ConcreteGroup := ProjectiveSpecialUnitaryMatrixGroup concreteForm

/-- The actual projective entrywise action, not an arbitrary outer actor. -/
def concreteActor : MulAut ConcreteGroup := entrywiseProjectiveAut concreteForm rfl

theorem concreteActor_entrywise : concreteForm.IsEntrywiseConjugation concreteActor :=
  entrywiseProjectiveAut_isEntrywiseConjugation concreteForm rfl

theorem concreteForm_conj (x : GaloisField 5 (2 * 1)) : concreteForm.conj x = x ^ 5 := by
  simp only [concreteForm, FormTransport.standardForm_conj, standardForm,
    ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]

/-- The remaining matrix existence problem. No maximality or generating
tuple is assumed here. -/
def ConcreteEmbedding : Prop :=
  ∀ [IsSimpleGroup ConcreteGroup],
    ∃ f : Perm (Fin 7) →* MulAut ConcreteGroup,
      Function.Injective f ∧
      (∀ q : alternatingGroup (Fin 7),
        f (q : Perm (Fin 7)) ∈ (MulAut.conj : ConcreteGroup →* MulAut ConcreteGroup).range) ∧
      f tripleSwap = concreteActor

/-- The independent extension problem, with the genuine A₇ embedding supplied
by its existing owner. The output may adjust that embedding to place the
marked odd involution at the prescribed entrywise action. -/
def ConcreteExtension : Prop :=
  ∀ [IsSimpleGroup ConcreteGroup],
    (∃ j : alternatingGroup (Fin 7) →* ConcreteGroup, Function.Injective j) →
    ∃ f : Perm (Fin 7) →* MulAut ConcreteGroup,
      Function.Injective f ∧
      (∀ q : alternatingGroup (Fin 7),
        f (q : Perm (Fin 7)) ∈ (MulAut.conj : ConcreteGroup →* MulAut ConcreteGroup).range) ∧
      f tripleSwap = concreteActor

/-- An embedding with the marked odd involution gives all three literal
inner conjugators, using the even conjugators in S₇. -/
theorem marked_generators {S : Type*} [Group S] (a : MulAut S)
    (f : Perm (Fin 7) →* MulAut S)
    (heven : ∀ q : alternatingGroup (Fin 7),
      f (q : Perm (Fin 7)) ∈ (MulAut.conj : S →* MulAut S).range)
    (hmark : f tripleSwap = a) :
    ∀ i, ∃ s : S, MulAut.conj s * a * (MulAut.conj s)⁻¹ = f (generators i) := by
  intro i
  obtain ⟨q, hq⟩ := generators_even_conjugate i
  obtain ⟨s, hs⟩ := heven q
  refine ⟨s, ?_⟩
  rw [hs, ← hmark, ← map_inv, ← map_mul, ← map_mul, hq]

/-- The generated S₇ image lies in precisely the marked actor's extension. -/
theorem marked_range_le {S : Type*} [Group S] (a : MulAut S)
    (f : Perm (Fin 7) →* MulAut S)
    (heven : ∀ q : alternatingGroup (Fin 7),
      f (q : Perm (Fin 7)) ∈ (MulAut.conj : S →* MulAut S).range)
    (hmark : f tripleSwap = a) : f.range ≤ MulAut.singleInnerExtension a := by
  rw [MonoidHom.range_eq_map, ← generators_generate, MonoidHom.map_closure]
  apply (closure_le _).mpr
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  obtain ⟨s, hs⟩ := marked_generators a f heven hmark i
  rw [← hs]
  have hi : MulAut.conj s ∈ MulAut.singleInnerExtension a :=
    (show (MulAut.conj : S →* MulAut S).range ≤ MulAut.singleInnerExtension a from le_sup_left)
      ⟨s, rfl⟩
  have ha : a ∈ MulAut.singleInnerExtension a :=
    (show closure {a} ≤ MulAut.singleInnerExtension a from le_sup_right) (subset_closure (by simp))
  exact (MulAut.singleInnerExtension a).mul_mem ((MulAut.singleInnerExtension a).mul_mem hi ha)
    ((MulAut.singleInnerExtension a).inv_mem hi)

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer
