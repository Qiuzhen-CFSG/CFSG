module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.DefectZero.IntegralData
public import Theory.RingTheory.PrimitiveRootReduction
public import Theory.Character.SimpleCriteria

/-!
# Distinguishing the four genuine coefficient reductions

Compatible integral lifts of ordinary rows 5, 6, 7 and 14 have pairwise
inequivalent reductions in characteristic eleven. The first row has
involution trace 5, whereas the next two have trace -3. Those two rows have
different fifth-root periods; their squared difference is 5, which stays
nonzero in the residue field. The final row has different natural dimension.

The proofs use the literal representatives and root choice of `OrdinaryData`
and actual coefficient maps. They do not assume irreducibility of any
reduction. Existence of the integral models and irreducibility after reduction
remain separate obligations. Source: Janko, J. Algebra 3 (1966), 147–186;
Feit, *The Representation Theory of Finite Groups*, IV.4.19–20, pp.159–160.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.DefectZero

variable {G R : Type*} [Group G] [Finite G] [CommRing R] [IsDomain R]
  {d : OrdinaryData G} (m : IntegralModels d R)

/-- The literal coefficient reductions on the prescribed coordinate spaces. -/
@[expose] public noncomputable def IntegralModels.reduction (i : Fin 4) :
    Representation ElevenClosure G (Fin (defectZeroDegree i) → ElevenClosure) :=
  Representation.mapCoefficients m.residue (m.rep i)

/-- The ordinary table certifies irreducibility before reduction. -/
public theorem IntegralModels.ordinary_irreducible (i : Fin 4) :
    Representation.IsIrreducible (Representation.mapCoefficients m.complex (m.rep i)) := by
  apply (irreducible_iff_character_norm_one _).mpr
  rw [← m.character_eq]
  exact (d.complete.1 (row i)).2

/-- The chosen integral root lifts the primitive root in the ordinary table. -/
public theorem IntegralModels.rootFive_primitive : IsPrimitiveRoot m.rootFive 5 := by
  apply IsPrimitiveRoot.of_map_of_injective (f := m.complex) _ m.complex_injective
  rw [m.rootFive_complex]
  exact d.rootFive_primitive

/-- The same root remains primitive after reduction to characteristic eleven. -/
public theorem IntegralModels.reduced_rootFive_primitive : IsPrimitiveRoot (m.residue m.rootFive) 5 := by
  apply m.rootFive_primitive.map_of_prime_ne_zero (by decide)
  exact (CharP.cast_eq_zero_iff ElevenClosure 11 5).not.mpr (by decide)

private theorem trace_complex (i : Fin 4) (j : Fin 15) :
    m.complex (LinearMap.trace R _ (m.rep i (d.representatives j))) =
      ordinaryValue d.rootFive d.rootNineteen (row i) j := by
  rw [← d.values (row i) j, m.character_eq i, d.classes_eq j]
  exact (Representation.mapCoefficients_trace m.complex (m.rep i) _).symm

/-- The four ordinary values at the involution column. -/
@[expose] public def involutionValue : Fin 4 → ℤ := ![5, -3, -3, 1]

/-- The four values at the first order-five column, with a common root. -/
@[expose] public def fifthValue {K : Type*} [CommRing K] (ζ : K) : Fin 4 → K :=
  ![2, ζ + ζ ^ 4, ζ ^ 2 + ζ ^ 3, -1]

/-- Reduction of the involution traces uses the actual table representatives. -/
public theorem IntegralModels.reduction_involution (i : Fin 4) :
    (m.reduction i).character (d.representatives 1) = (involutionValue i : ElevenClosure) := by
  have hi : LinearMap.trace R _ (m.rep i (d.representatives 1)) = (involutionValue i : R) := by
    apply m.complex_injective
    rw [trace_complex]
    fin_cases i <;> simp [row, involutionValue, ordinaryValue, map_ofNat]
  change LinearMap.trace ElevenClosure _ (Representation.mapCoefficients _ _ _) = _
  rw [Representation.mapCoefficients_trace, hi, map_intCast]

/-- Reduction of the order-five traces preserves their common root choice. -/
public theorem IntegralModels.reduction_fifth (i : Fin 4) :
    (m.reduction i).character (d.representatives 3) = fifthValue (m.residue m.rootFive) i := by
  have hi : LinearMap.trace R _ (m.rep i (d.representatives 3)) = fifthValue m.rootFive i := by
    apply m.complex_injective
    rw [trace_complex]
    fin_cases i <;> simp [row, fifthValue, ordinaryValue, m.rootFive_complex, map_ofNat]
  change LinearMap.trace ElevenClosure _ (Representation.mapCoefficients _ _ _) = _
  rw [Representation.mapCoefficients_trace, hi]
  fin_cases i <;> simp [fifthValue, map_ofNat]

/-- Involution traces separate the first degree-77 row from the next two;
the two fifth-root periods separate those remaining rows. Natural dimension
separates the degree-209 row. No irreducibility premise is needed here. -/
public theorem IntegralModels.reductions_inequivalent :
    Pairwise fun i j => IsEmpty ((m.reduction i).Equiv (m.reduction j)) := by
  intro i j hij
  constructor
  intro e
  have hd : defectZeroDegree i = defectZeroDegree j := by
    simpa only [Module.finrank_fin_fun] using e.toLinearEquiv.finrank_eq
  have ht := congrFun (Representation.char_iso e) (d.representatives 1)
  rw [m.reduction_involution, m.reduction_involution] at ht
  have hf := congrFun (Representation.char_iso e) (d.representatives 3)
  rw [m.reduction_fifth, m.reduction_fifth] at hf
  have hperiod := m.reduced_rootFive_primitive.fifth_periods_ne
    ((CharP.cast_eq_zero_iff ElevenClosure 11 5).not.mpr (by decide))
  have hsep : (5 : ElevenClosure) ≠ -3 := by
    intro h
    have he : (8 : ElevenClosure) = 0 := by linear_combination h
    exact (CharP.cast_eq_zero_iff ElevenClosure 11 8).not.mpr (by decide) he
  fin_cases i <;> fin_cases j <;>
    simp_all [defectZeroDegree, involutionValue, fifthValue, Ne.symm hperiod, Ne.symm hsep]

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.DefectZero
