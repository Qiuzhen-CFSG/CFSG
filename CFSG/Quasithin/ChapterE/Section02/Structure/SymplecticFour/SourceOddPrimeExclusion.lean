module
public import Theory.SpecificGroups.SymplecticFour.OddPrimeLinearExclusion
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceOddCore
public import CFSG.Quasithin.ClassicalModels

/-!
# The odd-prime exclusion on the original symplectic pair

The actual natural symplectic action excludes every PSL2(p) subgroup for
prime p>5. Restricting twice gives the same conclusion for the generalized
Fitting subgroup of the original opposition pair. The final adapter keeps
the source component inclusion and the original V comap literally.

This discharges the odd-prime row in Aschbacher--Smith E.2.7, printed p.220.
The known-simple shortlist, coefficient-field recognition and Bender subgroup
markings remain separate source results.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate
variable {F : Type*} [Field F] [CharP F 2]

/-- The odd-prime PSL2 candidate is impossible in every literal symplectic subgroup. -/
theorem subgroup_not_odd_prime_linear (I : Subgroup (Sp F)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 < p) : ¬ ClassicalGroup.IsPSL I 2 p := by
  rintro ⟨K,_,_,hK,⟨e⟩⟩
  exact odd_prime_psl2_not_injective hp hp5 hK (I.subtype.comp e.symm.toMonoidHom)
    (I.subtype_injective.comp e.symm.injective)

/-- The actual simple socle of a literal pair cannot be an odd-prime PSL2 candidate. -/
theorem pair_socle_not_odd_prime_linear (V : Subgroup (Sp F)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 < p) :
    ¬ ClassicalGroup.IsPSL (generalizedFitting (oppositePair V)) 2 p := by
  rintro ⟨K,_,_,hK,⟨e⟩⟩
  let I := oppositePair V
  let S := generalizedFitting I
  exact odd_prime_psl2_not_injective hp hp5 hK
    (I.subtype.comp (S.subtype.comp e.symm.toMonoidHom))
    (I.subtype_injective.comp (S.subtype_injective.comp e.symm.injective))

/-- Both the pair and its socle retain the original component coordinates;
the odd PSL2(p), p>5 row is excluded without a recognition hypothesis. -/
theorem source_aligned_pair_odd_prime_exclusion
    {G : Type*} [Group G] (L : Subgroup G) (e : Sp F ≃* L)
    (V : Subgroup G) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) :
    let W := V.comap (L.subtype.comp e.toMonoidHom)
    (¬ ClassicalGroup.IsPSL (oppositePair W) 2 p) ∧
      (¬ ClassicalGroup.IsPSL (generalizedFitting (oppositePair W)) 2 p) := by
  exact ⟨subgroup_not_odd_prime_linear _ hp hp5,
    pair_socle_not_odd_prime_linear _ hp hp5⟩

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
