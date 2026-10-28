module

public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticEncoding
public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticCertificateData

/-!
# Soundness of the finite unitary frames

The finite checks include every square and polar equation in the six-generator
presentation. They also express every vector and central element as a product
of the proposed generators, which implies the two required subgroup closures.
The candidate data originate in the change-of-basis orbit of MacWilliams's
unitary quadratic form (Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3).
-/

namespace MacWilliamsSylow.QuadraticCertificate

@[expose] public def quotientGenerators (r : UnitaryWitness) : Fin 6 → BinaryCoordinates 4 :=
  ![vector r.2.1, vector r.2.2.1, vector r.2.2.2.1, vector r.2.2.2.2.1, 1, 1]

@[expose] public def centralGenerators (r : UnitaryWitness) : Fin 6 → BinaryCoordinates 2 :=
  ![1, 1, 1, 1, central r.2.2.2.2.2.1, central r.2.2.2.2.2.2]

@[expose] public def rowChecks (r : UnitaryWitness) : Bool := decide (
    (∀ i, coordinateSquare (coefficients r.1) (quotientGenerators r i) =
      word (centralGenerators r) (unitaryTable.square i)) ∧
    (∀ i j, i < j →
      coordinatePolar (coefficients r.1) (quotientGenerators r j) (quotientGenerators r i) =
      word (centralGenerators r) (unitaryTable.commutator j i)) ∧
    (∀ n : Fin 16, ∃ t : Fin 16, vector n =
      ∏ i : Fin 4, if (BitVec.ofFin t).getLsb i then
        quotientGenerators r ⟨i.val, by omega⟩ else 1) ∧
    (∀ n : Fin 4, ∃ t : Fin 4, central n =
      ∏ i : Fin 2, if (BitVec.ofFin t).getLsb i then
        centralGenerators r ⟨i.val + 4, by omega⟩ else 1))

public theorem frame_of_rowChecks (r : UnitaryWitness) (h : rowChecks r = true) :
    Nonempty (UnitaryQuadraticFrame
      (coordinateSquare (coefficients r.1)) (coordinatePolar (coefficients r.1))) := by
  obtain ⟨hs, hp, hv, hz⟩ := of_decide_eq_true h
  refine ⟨{
    quotientGenerator := quotientGenerators r
    centralGenerator := centralGenerators r
    quotient_last := ?_
    central_first := ?_
    quotient_closure := ?_
    central_closure := ?_
    square_eq := hs
    polar_eq := hp }⟩
  · intro i hi
    fin_cases i <;> simp_all [quotientGenerators]
  · intro i hi
    fin_cases i <;> simp_all [centralGenerators]
  · apply top_unique
    intro y _
    obtain ⟨n, rfl⟩ := vector_bijective.2 y
    obtain ⟨t, ht⟩ := hv n
    rw [ht]
    apply Subgroup.prod_mem
    intro i _
    split_ifs
    · exact Subgroup.subset_closure ⟨_, rfl⟩
    · exact Subgroup.one_mem _
  · apply top_unique
    intro y _
    obtain ⟨n, rfl⟩ := central_bijective.2 y
    obtain ⟨t, ht⟩ := hz n
    rw [ht]
    apply Subgroup.prod_mem
    intro i _
    split_ifs
    · exact Subgroup.subset_closure ⟨_, rfl⟩
    · exact Subgroup.one_mem _

end MacWilliamsSylow.QuadraticCertificate
