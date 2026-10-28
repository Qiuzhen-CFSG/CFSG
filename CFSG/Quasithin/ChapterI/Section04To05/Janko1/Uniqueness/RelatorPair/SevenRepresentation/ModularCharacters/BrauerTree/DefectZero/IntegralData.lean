module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.Contracts
public import Theory.Representation.CoefficientReduction

/-!
# Integral inputs for the four defect-zero rows

The rows are 5, 6, 7 and 14 of the genuine ordinary table. Their degrees
divide 175560 with cofactors 2280, 2280, 2280 and 840, all prime to eleven.
The coefficient contract below asks for integral representations with these
ordinary characters, an embedding into the complex numbers and a reduction
to the literal `ElevenClosure`. It makes no modular irreducibility assertion.

Existence of these inputs is the invariant-lattice step of the defect-zero
reduction theorem (Serre, *Linear Representations of Finite Groups*, Chapter
15). The source application is Janko, J. Algebra 3 (1966), 147–186;
the ordinary row conventions are recorded in `../../Source.md`.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.DefectZero

/-- Ordinary rows of the four defect-zero modules. -/
@[expose] public def row : Fin 4 → Fin 15 := ![5, 6, 7, 14]

/-- The prime-to-eleven quotients of the group order by these degrees. -/
@[expose] public def cofactor : Fin 4 → ℕ := ![2280, 2280, 2280, 840]

public theorem ordinaryDegree_row (i : Fin 4) :
    ordinaryDegree (row i) = defectZeroDegree i := by
  fin_cases i <;> rfl

public theorem degree_pos (i : Fin 4) : 0 < defectZeroDegree i := by
  fin_cases i <;> decide

public theorem degree_mul_cofactor (i : Fin 4) :
    defectZeroDegree i * cofactor i = 175560 := by
  fin_cases i <;> decide

public theorem cofactor_cast_ne_zero (i : Fin 4) : (cofactor i : ElevenClosure) ≠ 0 := by
  apply (CharP.cast_eq_zero_iff ElevenClosure 11 (cofactor i)).not.mpr
  fin_cases i <;> decide

variable {G : Type*} [Group G] [Finite G]

/-- Compatible integral models, without assuming irreducibility of reductions.
The fifth root is the particular root used by `d`, so its two periods cannot
be exchanged independently in different rows. -/
public structure IntegralModels (d : OrdinaryData G) (R : Type*)
    [CommRing R] [IsDomain R] where
  complex : R →+* ℂ
  complex_injective : Function.Injective complex
  residue : R →+* ElevenClosure
  rootFive : R
  rootFive_complex : complex rootFive = d.rootFive
  rep : ∀ i, Representation R G (Fin (defectZeroDegree i) → R)
  character_eq : ∀ i, d.chi (row i) = characterClassFunction
    (Representation.mapCoefficients complex (rep i))

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.DefectZero
