module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Finitely many simple quotients of a finite-length module

A pairwise nonisomorphic family of actual simple modules admitting surjections
from a fixed finite-length module has finite index type. The ring, source,
indices, and target modules may lie in independent universes. No semisimplicity
or completeness assumption on the family is needed. This supplies the
finite-length input for constructing finite families of simple representations.

The proof is the elementary induction on the definition of `IsFiniteLength`
in Mathlib's `RingTheory.FiniteLength`. In a simple-quotient extension by `N`,
partition chosen surjections according to whether their restrictions to `N`
are nonzero. Such restrictions are surjective by simplicity, so induction
makes this part finite. The remaining maps descend to the simple module
`M ⧸ N`; Schur's lemma from `RingTheory.SimpleModule.Basic` makes them
isomorphisms, and pairwise nonisomorphism makes this part subsingleton.
A subsingleton source admits no surjection onto a simple module.
-/

universe u v w z

/-- A finite-length module has only finitely many pairwise nonisomorphic
simple quotients, with no universe restriction on the given family. -/
public theorem IsFiniteLength.finite_simple_quotients
    {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    (hLength : IsFiniteLength R M) {ι : Type w} (S : ι → Type z)
    [∀ index, AddCommGroup (S index)] [∀ index, Module R (S index)]
    [∀ index, IsSimpleModule R (S index)]
    (hDistinct : ∀ left right, Nonempty (S left ≃ₗ[R] S right) → left = right)
    (hQuotient : ∀ index, ∃ quotientMap : M →ₗ[R] S index,
      Function.Surjective quotientMap) : Finite ι := by
  classical
  induction hLength generalizing ι with
  | of_subsingleton =>
    have : IsEmpty ι := ⟨fun index => by
      obtain ⟨quotientMap, surjective⟩ := hQuotient index
      have : Subsingleton (S index) := surjective.subsingleton
      have : Nontrivial (S index) := IsSimpleModule.nontrivial R (S index)
      obtain ⟨left, right, distinct⟩ := exists_pair_ne (S index)
      exact distinct (Subsingleton.elim left right)⟩
    infer_instance
  | @of_simple_quotient M _ _ N _ _ inductionHyp =>
    choose quotientMap surjective using hQuotient
    let active : Set ι := {index | (quotientMap index).comp N.subtype ≠ 0}
    have : Finite active := inductionHyp (fun index : active => S index)
      (fun left right equiv => Subtype.ext (hDistinct left right equiv))
      (fun index => ⟨(quotientMap index).comp N.subtype,
        LinearMap.surjective_of_ne_zero index.property⟩)
    have descended : ∀ index : ↥(activeᶜ), Nonempty ((M ⧸ N) ≃ₗ[R] S index) := by
      intro index
      have restrictionZero : (quotientMap index).comp N.subtype = 0 :=
        not_ne_iff.mp index.property
      have contained : N ≤ LinearMap.ker (quotientMap index) := by
        intro vector mem
        exact DFunLike.congr_fun restrictionZero (⟨vector, mem⟩ : N)
      let descendedMap := N.liftQ (quotientMap index) contained
      have descendedSurjective : Function.Surjective descendedMap := by
        intro vector
        obtain ⟨preimage, equation⟩ := surjective index vector
        exact ⟨N.mkQ preimage, equation⟩
      have descendedNonzero : descendedMap ≠ 0 := by
        intro zero
        have : Nontrivial (S index) := IsSimpleModule.nontrivial R (S index)
        obtain ⟨vector, nonzero⟩ := exists_ne (0 : S index)
        obtain ⟨preimage, equation⟩ := descendedSurjective vector
        exact nonzero (equation.symm.trans (DFunLike.congr_fun zero preimage))
      exact ⟨LinearEquiv.ofBijective descendedMap
        (LinearMap.bijective_of_ne_zero descendedNonzero)⟩
    have : Subsingleton ↥(activeᶜ) := ⟨fun left right => by
      obtain ⟨leftEquiv⟩ := descended left
      obtain ⟨rightEquiv⟩ := descended right
      exact Subtype.ext (hDistinct left right ⟨leftEquiv.symm.trans rightEquiv⟩)⟩
    have finiteComplement : (activeᶜ).Finite := Set.Subsingleton.finite (by
      intro left memLeft right memRight
      exact congrArg Subtype.val
        (Subsingleton.elim (⟨left, memLeft⟩ : ↥(activeᶜ)) ⟨right, memRight⟩))
    exact (Set.toFinite active).finite_of_compl finiteComplement
