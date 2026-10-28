module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.DefectZero.TraceSeparation
public import Theory.Representation.DefectZeroReduction

/-!+# Irreducibility of the four defect-zero reductions

The compatible integral models of ordinary rows 5, 6, 7 and 14 have
irreducible complex extensions. Their degrees divide the group order 175560
with cofactors 2280, 2280, 2280 and 840, all nonzero in characteristic eleven.
The coefficient-reduction theorem therefore proves irreducibility of their
literal reductions over `ElevenClosure`.

The integral models remain explicit: their construction is the separate
existence input. Pairwise inequivalence is already proved by `TraceSeparation`.
Source: Feit, *The Representation Theory of Finite Groups*, IV.4.19–20,
printed pp.159–160; Janko, J. Algebra 3 (1966), 147–186.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.DefectZero

variable {G R : Type*} [Group G] [Finite G] [CommRing R] [IsDomain R]
  {d : OrdinaryData G}

/-- All four genuine coefficient reductions are irreducible. The ordinary
table supplies complex irreducibility, and the source group order supplies
the prime-to-eleven degree cofactors. -/
public theorem IntegralModels.reductions_irreducible (m : IntegralModels d R)
    (horder : Nat.card G = 175560) :
    ∀ i, Representation.IsIrreducible (m.reduction i) := by
  intro i
  exact Representation.isIrreducible_mapCoefficients_of_defectZero
    m.complex m.complex_injective m.residue (m.rep i) (m.ordinary_irreducible i)
    (degree_pos i) (horder.trans (degree_mul_cofactor i).symm) (cofactor_cast_ne_zero i)

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.DefectZero
