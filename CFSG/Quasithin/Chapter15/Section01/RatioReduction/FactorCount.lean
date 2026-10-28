module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.FactorCount
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SelectedAction

/-!
# The selected local action's conjugate-factor bound

The original subgroup M is an SQTK cover of its literal conjugation image.
Its rank bound supplies the factor-orbit conclusion without passing prime
rank through an arbitrary quotient. The D.2 splitting and classification
supply the displayed factors, prime cores and moving involution.

Source: Aschbacher--Smith 15.1.2, second paragraph, printed p.1084.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.RatioDecomposition ChapterD.UniqueFactor ChapterA.Section05To06 Stellmacher
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Original 15.1.2, paragraph two, on the literal quotient action of M.
The preceding splitting supplies the factors and their conjugacy orbit;
the original SQTK cover supplies the rank bound, without quotient rank monotonicity. -/
theorem source_localAction_factor_orbit_bound
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ (K : Subgroup D) (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (c : FactorData ρ K U) (d : Decomposition c.representation)
      (p : ℕ) [Fact p.Prime], Odd p →
      ∀ (P : Subgroup D) [P.Normal], IsPGroup p P →
      ∀ {ι : Type*} [Finite ι] (n : ι → d.Index), Function.Injective n →
      ∀ (R : ι → Subgroup D), (∀ j, R j ≤ (c.ambientFactor d (n j)).actor) →
      (∀ j, IsPGroup p (R j)) → (∀ j, R j ≠ ⊥) →
      (∀ j k, ∃ g : D, (R j).map (MulAut.conj g).toMonoidHom = R k) →
      ∀ (i : ι) (t : D), t ∈ (c.ambientFactor d (n i)).actor → orderOf t = 2 →
      t ∉ centralizer (P : Set D) → 1 < Nat.card ι →
      Nat.card ι = 2 ∧ ∀ j, IsCyclic (R j) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let f := actionHom M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro K U c d p hpFact hp P hPN hP ι hι n hn R hRle hR hne hconj i t htmem ht htP hmore
  exact c.factor_orbit_bound d hp f.rangeRestrict f.rangeRestrict_surjective
    ((Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1)).stronglyQuasithin
      p hpFact.out hp) P hP n hn R hRle hR hne hconj i t htmem ht htP hmore
end CFSG.Quasithin.Chapter15.Section01