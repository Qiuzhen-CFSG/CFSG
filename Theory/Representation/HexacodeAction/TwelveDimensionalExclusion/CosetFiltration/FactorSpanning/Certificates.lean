module

public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.FactorSpanning.Tools

/-!
# Kernel-checked rank-one and orbit-basis certificates

The witnesses in `../source/FactorCandidates.json` give a rank-one polynomial
and cyclic row and column bases for each published pair. All finite identities
below are checked by Lean's kernel using the arithmetic interpretation in Tools.
The generator tables are explicitly compared with the fixed `factorMatrix`.

Source application: Aschbacher–Smith K.1.3, printed p.453 / PDF p.464.
The underlying hexacode matrices are from Gerald Höhn and the ATLAS contributors;
see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public section
namespace Representation.Hexacode.TwelveDimensional.CosetCertificate.Spanning

namespace Factor0

private def generators : Fin 2 → MatCodes 3 :=
  ![![![0,0,1],
    ![3,1,2],
    ![1,0,0]],
    ![![0,1,0],
    ![1,1,0],
    ![2,2,1]]]

private def cols : MatCodes 3 :=
  ![![0,1,0],
    ![1,1,2],
    ![2,1,1]]

private def rows : MatCodes 3 :=
  ![![1,0,1],
    ![2,3,1],
    ![3,3,3]]

private def ci : MatCodes 3 :=
  ![![2,3,1],
    ![1,0,0],
    ![2,1,3]]

private def ri : MatCodes 3 :=
  ![![3,2,2],
    ![1,0,2],
    ![2,2,2]]

private def cp : Fin 2 → Fin 3 := ![0,1]
private def ca : Fin 2 → Fin 2 := ![1,0]
private def rp : Fin 2 → Fin 3 := ![0,1]
private def ra : Fin 2 → Fin 2 := ![1,0]

private theorem rankOne_mem (Q : Subalgebra F (Matrix (Fin 3) (Fin 3) F))
    (hA : ∀ j, matrix (generators j) ∈ Q) :
    matrix (rankOne (cols 0) (rows 0)) ∈ Q := by
  have hn := plus_scalar_mem Q (generators 0) 1 (hA 0)
  exact product_mem Q _ _ _ hn hn (by decide +kernel)

private theorem generators_eq (j : Fin 2) :
    matrix (generators j) = factorMatrix 0 j := by
  have h : ∀ (j : Fin 2) (i k : Fin 3), generators j i k =
      adaptedRows j (blockIndex 0 i) (blockIndex 0 k) := by decide +kernel
  funext i k
  exact congrArg entry (h j i k)

/-- The literal published factor pair generates its full matrix algebra. -/
theorem full (Q : Subalgebra F (Matrix (Fin (degree 0)) (Fin (degree 0)) F))
    (hQ : ∀ j, factorMatrix 0 j ∈ Q) : Q = ⊤ := by
  have hA : ∀ j, matrix (generators j) ∈ Q := fun j => (generators_eq j).symm ▸ hQ j
  exact full_of_orbits Q generators hA cols rows ci ri cp rp ca ra
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (rankOne_mem Q hA)

end Factor0

namespace Factor1

private def generators : Fin 2 → MatCodes 9 :=
  ![![![1,0,1,3,0,0,2,2,3],
    ![0,0,0,0,0,3,1,0,0],
    ![3,0,2,1,0,1,0,3,3],
    ![3,1,3,2,0,0,2,1,1],
    ![1,0,0,3,0,0,2,2,2],
    ![3,0,3,3,0,2,3,1,1],
    ![3,1,1,2,1,1,2,3,0],
    ![1,3,2,1,3,2,1,3,2],
    ![2,0,2,1,1,1,0,3,3]],
    ![![0,3,3,2,3,3,0,0,2],
    ![1,3,3,2,2,3,0,0,2],
    ![1,0,3,3,2,2,0,1,2],
    ![1,2,0,1,2,1,1,1,1],
    ![0,3,0,3,0,1,2,2,2],
    ![0,0,1,0,1,3,0,2,1],
    ![1,3,0,0,1,1,0,0,0],
    ![3,0,0,3,2,0,0,0,2],
    ![1,0,0,2,1,0,1,0,2]]]

private def cols : MatCodes 9 :=
  ![![0,3,3,3,0,0,3,1,3],
    ![0,0,0,3,2,2,2,3,3],
    ![2,3,1,2,1,0,0,0,3],
    ![0,2,0,0,3,1,0,0,0],
    ![0,0,3,1,2,0,1,2,0],
    ![0,3,3,0,2,3,1,3,1],
    ![0,3,1,2,0,2,0,1,2],
    ![1,1,1,0,2,0,0,1,3],
    ![1,3,0,1,2,2,2,0,1]]

private def rows : MatCodes 9 :=
  ![![0,1,0,1,0,1,0,0,0],
    ![0,1,2,3,1,1,1,3,2],
    ![2,0,1,0,1,1,0,1,1],
    ![1,2,3,2,3,0,3,1,3],
    ![0,3,3,0,2,0,3,3,0],
    ![3,2,3,2,1,1,3,1,2],
    ![3,2,1,2,3,0,2,0,2],
    ![1,1,3,0,1,3,2,1,0],
    ![1,1,0,0,2,2,3,0,2]]

private def ci : MatCodes 9 :=
  ![![3,1,3,1,1,0,1,3,3],
    ![3,3,0,3,3,1,0,3,3],
    ![0,2,2,1,2,0,2,0,3],
    ![0,1,0,1,3,0,1,3,3],
    ![1,0,0,3,2,0,1,3,3],
    ![2,1,0,2,0,2,3,3,3],
    ![2,0,0,0,3,3,1,0,0],
    ![0,0,3,2,2,2,2,1,0],
    ![3,0,3,0,2,1,1,2,3]]

private def ri : MatCodes 9 :=
  ![![1,1,0,1,3,3,3,3,3],
    ![2,2,0,3,3,2,3,2,2],
    ![1,3,2,1,2,3,0,3,3],
    ![3,3,2,1,2,0,1,0,1],
    ![1,1,3,2,1,3,0,2,3],
    ![0,1,2,2,1,2,2,2,3],
    ![2,2,1,2,1,3,3,2,2],
    ![2,0,1,1,1,0,0,2,1],
    ![0,1,3,2,2,3,3,0,3]]

private def cp : Fin 8 → Fin 9 := ![0,1,1,2,2,3,4,4]
private def ca : Fin 8 → Fin 2 := ![1,0,1,0,1,0,0,1]
private def rp : Fin 8 → Fin 9 := ![0,1,1,2,2,3,4,4]
private def ra : Fin 8 → Fin 2 := ![1,0,1,0,1,0,0,1]

private def p2 : MatCodes 9 :=
  ![![3,0,1,1,0,3,2,0,2],
    ![1,0,3,0,1,0,0,0,3],
    ![0,3,1,1,1,2,3,0,0],
    ![2,3,1,0,0,1,1,0,3],
    ![3,0,1,1,0,3,2,0,2],
    ![3,3,2,0,1,1,1,0,0],
    ![1,2,0,0,0,3,3,0,1],
    ![2,2,3,3,1,1,2,0,0],
    ![0,3,1,1,1,2,3,0,0]]

private def p3 : MatCodes 9 :=
  ![![0,3,0,3,0,3,0,0,0],
    ![2,0,2,0,2,0,0,0,2],
    ![2,1,2,1,2,1,0,0,2],
    ![2,2,2,2,2,2,0,0,2],
    ![0,3,0,3,0,3,0,0,0],
    ![0,2,0,2,0,2,0,0,0],
    ![2,1,2,1,2,1,0,0,2],
    ![3,3,3,3,3,3,0,0,3],
    ![2,1,2,1,2,1,0,0,2]]

private def p4 : MatCodes 9 :=
  ![![0,0,1,1,3,0,3,2,1],
    ![2,0,2,0,2,0,1,1,2],
    ![2,0,0,2,3,0,0,2,0],
    ![2,0,1,3,0,0,3,0,1],
    ![0,0,1,1,3,0,3,2,1],
    ![0,0,3,3,2,0,2,1,3],
    ![2,0,0,2,3,0,0,2,0],
    ![3,0,2,1,0,0,1,0,2],
    ![2,0,0,2,3,0,0,2,0]]

private def p5 : MatCodes 9 :=
  ![![3,2,1,1,0,3,0,2,1],
    ![1,3,3,3,0,1,3,3,1],
    ![0,0,1,1,0,0,3,0,3],
    ![3,2,0,0,0,3,3,2,2],
    ![3,2,1,1,0,3,0,2,1],
    ![2,1,3,3,0,2,0,1,3],
    ![0,0,1,1,0,0,3,0,3],
    ![1,3,0,0,0,1,1,3,3],
    ![0,0,1,1,0,0,3,0,3]]

private theorem rankOne_mem (Q : Subalgebra F (Matrix (Fin 9) (Fin 9) F))
    (hA : ∀ j, matrix (generators j) ∈ Q) :
    matrix (rankOne (cols 0) (rows 0)) ∈ Q := by
  have hn := plus_scalar_mem Q (generators 0) 1 (hA 0)
  have hb := plus_scalar_mem Q (generators 1) 1 (hA 1)
  have hw := plus_scalar_mem Q (generators 1) 2 (hA 1)
  have h2 := product_mem Q _ _ p2 hn hn (by decide +kernel)
  have h3 := product_mem Q _ _ p3 h2 hn (by decide +kernel)
  have h4 := product_mem Q _ _ p4 h3 hb (by decide +kernel)
  have h5 := product_mem Q _ _ p5 h4 hw (by decide +kernel)
  exact product_mem Q _ _ _ h5 h3 (by decide +kernel)

private theorem generators_eq (j : Fin 2) :
    matrix (generators j) = factorMatrix 1 j := by
  have h : ∀ (j : Fin 2) (i k : Fin 9), generators j i k =
      adaptedRows j (blockIndex 1 i) (blockIndex 1 k) := by decide +kernel
  funext i k
  exact congrArg entry (h j i k)

/-- The literal published factor pair generates its full matrix algebra. -/
theorem full (Q : Subalgebra F (Matrix (Fin (degree 1)) (Fin (degree 1)) F))
    (hQ : ∀ j, factorMatrix 1 j ∈ Q) : Q = ⊤ := by
  have hA : ∀ j, matrix (generators j) ∈ Q := fun j => (generators_eq j).symm ▸ hQ j
  exact full_of_orbits Q generators hA cols rows ci ri cp rp ca ra
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (rankOne_mem Q hA)

end Factor1

namespace Factor2

private def generators : Fin 2 → MatCodes 3 :=
  ![![![1,1,1],
    ![1,0,0],
    ![0,1,0]],
    ![![1,0,0],
    ![2,2,0],
    ![1,1,3]]]

private def cols : MatCodes 3 :=
  ![![1,1,1],
    ![1,0,3],
    ![2,1,0]]

private def rows : MatCodes 3 :=
  ![![1,0,1],
    ![0,1,3],
    ![1,3,0]]

private def ci : MatCodes 3 :=
  ![![1,2,1],
    ![2,3,3],
    ![2,1,2]]

private def ri : MatCodes 3 :=
  ![![3,1,2],
    ![1,2,1],
    ![2,1,2]]

private def cp : Fin 2 → Fin 3 := ![0,1]
private def ca : Fin 2 → Fin 2 := ![1,0]
private def rp : Fin 2 → Fin 3 := ![0,1]
private def ra : Fin 2 → Fin 2 := ![1,0]

private theorem rankOne_mem (Q : Subalgebra F (Matrix (Fin 3) (Fin 3) F))
    (hA : ∀ j, matrix (generators j) ∈ Q) :
    matrix (rankOne (cols 0) (rows 0)) ∈ Q := by
  have hn := plus_scalar_mem Q (generators 0) 1 (hA 0)
  exact product_mem Q _ _ _ hn hn (by decide +kernel)

private theorem generators_eq (j : Fin 2) :
    matrix (generators j) = factorMatrix 2 j := by
  have h : ∀ (j : Fin 2) (i k : Fin 3), generators j i k =
      adaptedRows j (blockIndex 2 i) (blockIndex 2 k) := by decide +kernel
  funext i k
  exact congrArg entry (h j i k)

/-- The literal published factor pair generates its full matrix algebra. -/
theorem full (Q : Subalgebra F (Matrix (Fin (degree 2)) (Fin (degree 2)) F))
    (hQ : ∀ j, factorMatrix 2 j ∈ Q) : Q = ⊤ := by
  have hA : ∀ j, matrix (generators j) ∈ Q := fun j => (generators_eq j).symm ▸ hQ j
  exact full_of_orbits Q generators hA cols rows ci ri cp rp ca ra
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (rankOne_mem Q hA)

end Factor2

namespace Factor3

private def generators : Fin 2 → MatCodes 3 :=
  ![![![0,2,1],
    ![3,0,3],
    ![1,2,1]],
    ![![0,2,0],
    ![2,0,2],
    ![2,2,0]]]

private def cols : MatCodes 3 :=
  ![![1,3,0],
    ![1,2,3],
    ![0,1,1]]

private def rows : MatCodes 3 :=
  ![![1,2,0],
    ![3,2,3],
    ![2,0,1]]

private def ci : MatCodes 3 :=
  ![![3,2,1],
    ![3,3,2],
    ![3,3,3]]

private def ri : MatCodes 3 :=
  ![![2,2,1],
    ![2,1,3],
    ![3,3,3]]

private def cp : Fin 2 → Fin 3 := ![0,1]
private def ca : Fin 2 → Fin 2 := ![1,0]
private def rp : Fin 2 → Fin 3 := ![0,1]
private def ra : Fin 2 → Fin 2 := ![1,0]

private theorem rankOne_mem (Q : Subalgebra F (Matrix (Fin 3) (Fin 3) F))
    (hA : ∀ j, matrix (generators j) ∈ Q) :
    matrix (rankOne (cols 0) (rows 0)) ∈ Q := by
  have hn := plus_scalar_mem Q (generators 0) 1 (hA 0)
  exact product_mem Q _ _ _ hn hn (by decide +kernel)

private theorem generators_eq (j : Fin 2) :
    matrix (generators j) = factorMatrix 3 j := by
  have h : ∀ (j : Fin 2) (i k : Fin 3), generators j i k =
      adaptedRows j (blockIndex 3 i) (blockIndex 3 k) := by decide +kernel
  funext i k
  exact congrArg entry (h j i k)

/-- The literal published factor pair generates its full matrix algebra. -/
theorem full (Q : Subalgebra F (Matrix (Fin (degree 3)) (Fin (degree 3)) F))
    (hQ : ∀ j, factorMatrix 3 j ∈ Q) : Q = ⊤ := by
  have hA : ∀ j, matrix (generators j) ∈ Q := fun j => (generators_eq j).symm ▸ hQ j
  exact full_of_orbits Q generators hA cols rows ci ri cp rp ca ra
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (rankOne_mem Q hA)

end Factor3

namespace Factor4

private def generators : Fin 2 → MatCodes 3 :=
  ![![![1,0,0],
    ![3,1,0],
    ![0,2,1]],
    ![![3,2,3],
    ![3,2,1],
    ![1,2,1]]]

private def cols : MatCodes 3 :=
  ![![0,0,1],
    ![3,1,1],
    ![3,3,3]]

private def rows : MatCodes 3 :=
  ![![1,0,0],
    ![3,2,3],
    ![2,3,3]]

private def ci : MatCodes 3 :=
  ![![0,3,1],
    ![1,3,3],
    ![1,0,0]]

private def ri : MatCodes 3 :=
  ![![1,0,0],
    ![1,1,1],
    ![2,1,3]]

private def cp : Fin 2 → Fin 3 := ![0,1]
private def ca : Fin 2 → Fin 2 := ![1,0]
private def rp : Fin 2 → Fin 3 := ![0,1]
private def ra : Fin 2 → Fin 2 := ![1,0]

private theorem rankOne_mem (Q : Subalgebra F (Matrix (Fin 3) (Fin 3) F))
    (hA : ∀ j, matrix (generators j) ∈ Q) :
    matrix (rankOne (cols 0) (rows 0)) ∈ Q := by
  have hn := plus_scalar_mem Q (generators 0) 1 (hA 0)
  exact product_mem Q _ _ _ hn hn (by decide +kernel)

private theorem generators_eq (j : Fin 2) :
    matrix (generators j) = factorMatrix 4 j := by
  have h : ∀ (j : Fin 2) (i k : Fin 3), generators j i k =
      adaptedRows j (blockIndex 4 i) (blockIndex 4 k) := by decide +kernel
  funext i k
  exact congrArg entry (h j i k)

/-- The literal published factor pair generates its full matrix algebra. -/
theorem full (Q : Subalgebra F (Matrix (Fin (degree 4)) (Fin (degree 4)) F))
    (hQ : ∀ j, factorMatrix 4 j ∈ Q) : Q = ⊤ := by
  have hA : ∀ j, matrix (generators j) ∈ Q := fun j => (generators_eq j).symm ▸ hQ j
  exact full_of_orbits Q generators hA cols rows ci ri cp rp ca ra
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (rankOne_mem Q hA)

end Factor4

namespace Factor5

private def generators : Fin 2 → MatCodes 9 :=
  ![![![1,3,2,3,3,0,0,2,3],
    ![0,0,3,0,3,0,2,0,0],
    ![2,1,2,1,0,0,2,1,1],
    ![0,3,2,3,0,0,0,3,3],
    ![2,3,2,1,0,0,1,1,1],
    ![0,0,0,1,3,0,3,0,0],
    ![1,0,3,3,3,3,3,0,0],
    ![0,0,0,0,0,1,3,0,0],
    ![0,2,3,3,1,0,1,1,2]],
    ![![2,2,0,2,1,2,0,1,2],
    ![0,1,0,0,1,2,3,1,3],
    ![1,3,3,1,2,2,0,2,3],
    ![3,0,3,3,0,2,3,1,2],
    ![1,0,3,3,2,1,1,0,2],
    ![1,0,2,0,1,3,0,2,1],
    ![0,0,2,3,1,2,3,2,1],
    ![0,3,1,3,2,3,2,3,1],
    ![0,0,3,3,3,2,0,2,2]]]

private def cols : MatCodes 9 :=
  ![![3,0,2,3,2,2,0,2,1],
    ![1,0,1,2,3,1,2,2,0],
    ![3,2,3,2,2,1,3,0,1],
    ![2,2,0,0,1,0,0,0,1],
    ![0,2,0,2,1,1,0,3,3],
    ![3,3,0,3,3,2,3,3,2],
    ![3,3,0,2,3,3,1,0,0],
    ![0,3,0,0,3,1,1,1,1],
    ![1,0,0,1,3,0,0,0,0]]

private def rows : MatCodes 9 :=
  ![![1,0,3,0,2,1,2,0,3],
    ![2,0,0,3,2,0,3,0,1],
    ![2,0,0,0,2,2,1,2,3],
    ![3,3,1,1,1,3,2,2,0],
    ![0,1,1,0,0,1,2,2,2],
    ![3,2,0,2,3,2,2,3,0],
    ![1,3,0,3,3,3,0,2,1],
    ![0,2,1,0,3,3,1,3,2],
    ![0,3,1,0,2,2,1,0,2]]

private def ci : MatCodes 9 :=
  ![![3,1,0,0,3,0,3,1,0],
    ![3,2,1,1,0,1,2,1,3],
    ![3,0,0,1,3,3,3,1,0],
    ![1,3,2,2,1,2,0,1,3],
    ![3,3,3,3,3,3,1,0,3],
    ![2,2,2,3,0,3,2,2,0],
    ![1,0,3,0,2,0,0,3,1],
    ![0,3,1,2,2,3,3,3,3],
    ![3,2,1,0,2,1,3,0,2]]

private def ri : MatCodes 9 :=
  ![![2,1,3,1,3,2,2,0,3],
    ![0,3,3,3,3,3,0,1,1],
    ![1,2,2,3,3,2,2,2,0],
    ![2,1,0,3,0,2,3,2,0],
    ![2,2,2,0,0,3,0,2,3],
    ![0,1,0,3,2,0,0,3,2],
    ![3,2,2,1,3,0,0,0,0],
    ![3,0,2,0,2,0,0,2,2],
    ![3,2,3,3,3,3,1,2,0]]

private def cp : Fin 8 → Fin 9 := ![0,1,1,2,2,3,4,4]
private def ca : Fin 8 → Fin 2 := ![1,0,1,0,1,0,0,1]
private def rp : Fin 8 → Fin 9 := ![0,1,1,2,2,3,4,4]
private def ra : Fin 8 → Fin 2 := ![1,0,1,0,1,0,0,1]

private def p2 : MatCodes 9 :=
  ![![2,0,1,2,2,2,3,2,1],
    ![2,0,1,1,1,1,3,0,0],
    ![3,2,2,2,2,0,2,3,2],
    ![3,1,2,3,1,3,3,3,1],
    ![0,2,0,0,0,2,3,3,2],
    ![2,1,1,2,2,3,1,0,0],
    ![2,0,1,0,3,2,3,0,1],
    ![3,0,2,3,1,2,1,1,0],
    ![2,1,1,2,0,2,1,2,2]]

private def p3 : MatCodes 9 :=
  ![![2,2,1,2,1,2,0,2,0],
    ![3,0,2,0,1,3,1,0,2],
    ![2,1,1,1,2,2,1,1,2],
    ![2,2,1,2,1,2,0,2,0],
    ![3,1,2,1,0,3,3,1,1],
    ![0,1,0,1,1,0,2,1,3],
    ![0,0,0,0,0,0,0,0,0],
    ![0,1,0,1,1,0,2,1,3],
    ![3,3,2,3,2,3,0,3,0]]

private def p4 : MatCodes 9 :=
  ![![2,1,1,3,0,2,2,0,0],
    ![2,0,2,2,0,3,3,0,1],
    ![3,3,1,0,0,2,2,0,1],
    ![2,1,1,3,0,2,2,0,0],
    ![0,3,2,3,0,3,3,0,3],
    ![2,3,0,1,0,0,0,0,2],
    ![0,0,0,0,0,0,0,0,0],
    ![2,3,0,1,0,0,0,0,2],
    ![3,2,2,1,0,3,3,0,0]]

private def p5 : MatCodes 9 :=
  ![![1,3,3,0,1,3,3,2,2],
    ![0,2,0,2,2,3,2,1,1],
    ![3,0,2,2,1,1,0,0,0],
    ![1,3,3,0,1,3,3,2,2],
    ![3,3,2,1,2,0,3,2,2],
    ![3,1,2,3,0,3,1,3,3],
    ![0,0,0,0,0,0,0,0,0],
    ![3,1,2,3,0,3,1,3,3],
    ![2,1,1,0,2,1,1,3,3]]

private theorem rankOne_mem (Q : Subalgebra F (Matrix (Fin 9) (Fin 9) F))
    (hA : ∀ j, matrix (generators j) ∈ Q) :
    matrix (rankOne (cols 0) (rows 0)) ∈ Q := by
  have hn := plus_scalar_mem Q (generators 0) 1 (hA 0)
  have hb := plus_scalar_mem Q (generators 1) 1 (hA 1)
  have hw := plus_scalar_mem Q (generators 1) 2 (hA 1)
  have h2 := product_mem Q _ _ p2 hn hn (by decide +kernel)
  have h3 := product_mem Q _ _ p3 h2 hn (by decide +kernel)
  have h4 := product_mem Q _ _ p4 h3 hb (by decide +kernel)
  have h5 := product_mem Q _ _ p5 h4 hw (by decide +kernel)
  exact product_mem Q _ _ _ h5 h3 (by decide +kernel)

private theorem generators_eq (j : Fin 2) :
    matrix (generators j) = factorMatrix 5 j := by
  have h : ∀ (j : Fin 2) (i k : Fin 9), generators j i k =
      adaptedRows j (blockIndex 5 i) (blockIndex 5 k) := by decide +kernel
  funext i k
  exact congrArg entry (h j i k)

/-- The literal published factor pair generates its full matrix algebra. -/
theorem full (Q : Subalgebra F (Matrix (Fin (degree 5)) (Fin (degree 5)) F))
    (hQ : ∀ j, factorMatrix 5 j ∈ Q) : Q = ⊤ := by
  have hA : ∀ j, matrix (generators j) ∈ Q := fun j => (generators_eq j).symm ▸ hQ j
  exact full_of_orbits Q generators hA cols rows ci ri cp rp ca ra
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (rankOne_mem Q hA)

end Factor5

namespace Factor6

private def generators : Fin 2 → MatCodes 3 :=
  ![![![0,0,2],
    ![3,2,2],
    ![3,3,3]],
    ![![1,1,2],
    ![0,2,2],
    ![0,0,3]]]

private def cols : MatCodes 3 :=
  ![![1,3,3],
    ![3,0,2],
    ![3,1,3]]

private def rows : MatCodes 3 :=
  ![![0,1,1],
    ![0,2,1],
    ![2,0,0]]

private def ci : MatCodes 3 :=
  ![![1,3,3],
    ![2,3,0],
    ![2,2,1]]

private def ri : MatCodes 3 :=
  ![![0,0,3],
    ![2,2,0],
    ![3,2,0]]

private def cp : Fin 2 → Fin 3 := ![0,1]
private def ca : Fin 2 → Fin 2 := ![1,0]
private def rp : Fin 2 → Fin 3 := ![0,1]
private def ra : Fin 2 → Fin 2 := ![1,0]

private theorem rankOne_mem (Q : Subalgebra F (Matrix (Fin 3) (Fin 3) F))
    (hA : ∀ j, matrix (generators j) ∈ Q) :
    matrix (rankOne (cols 0) (rows 0)) ∈ Q := by
  have hn := plus_scalar_mem Q (generators 0) 1 (hA 0)
  exact product_mem Q _ _ _ hn hn (by decide +kernel)

private theorem generators_eq (j : Fin 2) :
    matrix (generators j) = factorMatrix 6 j := by
  have h : ∀ (j : Fin 2) (i k : Fin 3), generators j i k =
      adaptedRows j (blockIndex 6 i) (blockIndex 6 k) := by decide +kernel
  funext i k
  exact congrArg entry (h j i k)

/-- The literal published factor pair generates its full matrix algebra. -/
theorem full (Q : Subalgebra F (Matrix (Fin (degree 6)) (Fin (degree 6)) F))
    (hQ : ∀ j, factorMatrix 6 j ∈ Q) : Q = ⊤ := by
  have hA : ∀ j, matrix (generators j) ∈ Q := fun j => (generators_eq j).symm ▸ hQ j
  exact full_of_orbits Q generators hA cols rows ci ri cp rp ca ra
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (rankOne_mem Q hA)

end Factor6

namespace Factor7

private def generators : Fin 2 → MatCodes 9 :=
  ![![![0,0,0,3,3,2,2,2,1],
    ![2,2,1,3,3,2,0,1,0],
    ![2,2,1,3,3,2,2,0,2],
    ![0,1,3,1,1,3,3,3,0],
    ![2,3,1,3,3,2,0,1,0],
    ![1,1,2,3,3,2,2,0,0],
    ![1,1,3,3,2,1,0,1,1],
    ![0,0,0,0,1,0,0,1,0],
    ![0,0,0,2,2,0,2,3,3]],
    ![![0,1,0,2,0,0,3,1,1],
    ![3,3,1,2,2,0,1,2,2],
    ![2,0,0,1,1,0,1,0,1],
    ![0,0,0,0,1,3,1,1,2],
    ![0,0,0,0,1,0,2,3,1],
    ![2,2,1,0,3,2,2,1,1],
    ![0,0,0,2,1,2,2,0,0],
    ![1,1,3,3,1,0,1,0,0],
    ![0,0,0,3,2,3,0,2,2]]]

private def cols : MatCodes 9 :=
  ![![3,0,2,1,0,0,2,0,3],
    ![0,1,1,3,0,3,1,3,2],
    ![2,3,1,2,2,2,2,3,0],
    ![2,0,0,3,2,1,2,1,2],
    ![1,3,3,2,0,3,1,1,1],
    ![2,1,1,2,3,1,1,3,2],
    ![2,3,2,0,3,0,1,3,3],
    ![1,1,0,1,2,1,2,1,1],
    ![3,0,0,0,0,3,0,0,3]]

private def rows : MatCodes 9 :=
  ![![1,2,3,2,1,1,0,3,0],
    ![1,1,1,0,3,3,3,2,2],
    ![1,2,0,2,3,1,2,0,1],
    ![2,1,3,0,0,1,0,1,1],
    ![1,0,3,2,0,1,3,3,0],
    ![3,2,3,1,1,3,3,1,1],
    ![2,2,0,1,0,2,2,0,0],
    ![3,1,2,2,2,3,0,3,3],
    ![0,0,3,2,2,2,2,2,0]]

private def ci : MatCodes 9 :=
  ![![1,0,3,2,0,1,0,3,2],
    ![2,2,1,1,0,2,1,1,2],
    ![2,0,0,0,1,1,0,2,0],
    ![2,2,3,0,2,0,2,0,2],
    ![1,0,3,1,0,3,1,2,2],
    ![2,2,0,0,1,3,3,0,0],
    ![3,2,2,0,2,0,0,2,2],
    ![3,3,0,3,1,3,1,0,2],
    ![3,2,3,2,1,2,3,3,0]]

private def ri : MatCodes 9 :=
  ![![2,3,3,3,0,2,0,1,1],
    ![0,2,1,0,3,0,1,3,2],
    ![1,2,3,1,0,3,1,3,0],
    ![3,3,2,0,2,2,0,2,3],
    ![1,2,0,1,1,0,1,3,0],
    ![0,1,0,1,0,3,3,0,0],
    ![0,2,3,2,2,0,1,3,1],
    ![0,1,0,0,1,0,1,3,1],
    ![0,2,2,2,2,2,0,0,1]]

private def cp : Fin 8 → Fin 9 := ![0,1,1,2,2,3,4,4]
private def ca : Fin 8 → Fin 2 := ![1,0,1,0,1,0,0,1]
private def rp : Fin 8 → Fin 9 := ![0,1,1,2,2,3,4,4]
private def ra : Fin 8 → Fin 2 := ![1,0,1,0,1,0,0,1]

private def p2 : MatCodes 9 :=
  ![![0,1,3,3,3,2,3,2,1],
    ![2,3,1,3,2,2,0,1,0],
    ![0,0,1,1,3,0,3,3,3],
    ![1,1,3,2,3,0,3,3,2],
    ![0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,2,0,0,0,0],
    ![1,0,0,1,0,2,0,1,3],
    ![2,3,1,3,2,2,0,1,0],
    ![1,1,2,3,2,0,0,0,1]]

private def p3 : MatCodes 9 :=
  ![![3,2,1,2,3,2,1,0,0],
    ![0,0,0,0,0,0,0,0,0],
    ![0,2,2,2,0,3,3,1,0],
    ![0,1,1,1,0,2,2,3,0],
    ![0,0,0,0,0,0,0,0,0],
    ![3,1,2,1,3,3,0,2,0],
    ![3,3,0,3,3,0,3,3,0],
    ![0,0,0,0,0,0,0,0,0],
    ![3,2,1,2,3,2,1,0,0]]

private def p4 : MatCodes 9 :=
  ![![3,3,1,3,0,2,2,2,3],
    ![0,0,0,0,0,0,0,0,0],
    ![2,3,0,1,3,2,0,3,1],
    ![1,2,0,3,2,1,0,2,3],
    ![0,0,0,0,0,0,0,0,0],
    ![0,2,1,1,1,1,2,3,1],
    ![2,1,1,0,2,3,2,0,0],
    ![0,0,0,0,0,0,0,0,0],
    ![3,3,1,3,0,2,2,2,3]]

private def p5 : MatCodes 9 :=
  ![![0,1,2,0,3,3,2,1,0],
    ![0,0,0,0,0,0,0,0,0],
    ![1,1,3,1,2,0,2,1,0],
    ![3,3,2,3,1,0,1,3,0],
    ![0,0,0,0,0,0,0,0,0],
    ![2,3,3,2,0,3,1,3,0],
    ![3,2,0,3,2,3,3,2,0],
    ![0,0,0,0,0,0,0,0,0],
    ![0,1,2,0,3,3,2,1,0]]

private theorem rankOne_mem (Q : Subalgebra F (Matrix (Fin 9) (Fin 9) F))
    (hA : ∀ j, matrix (generators j) ∈ Q) :
    matrix (rankOne (cols 0) (rows 0)) ∈ Q := by
  have hn := plus_scalar_mem Q (generators 0) 1 (hA 0)
  have hb := plus_scalar_mem Q (generators 1) 1 (hA 1)
  have hw := plus_scalar_mem Q (generators 1) 2 (hA 1)
  have h2 := product_mem Q _ _ p2 hn hn (by decide +kernel)
  have h3 := product_mem Q _ _ p3 h2 hn (by decide +kernel)
  have h4 := product_mem Q _ _ p4 h3 hb (by decide +kernel)
  have h5 := product_mem Q _ _ p5 h4 hw (by decide +kernel)
  exact product_mem Q _ _ _ h5 h3 (by decide +kernel)

private theorem generators_eq (j : Fin 2) :
    matrix (generators j) = factorMatrix 7 j := by
  have h : ∀ (j : Fin 2) (i k : Fin 9), generators j i k =
      adaptedRows j (blockIndex 7 i) (blockIndex 7 k) := by decide +kernel
  funext i k
  exact congrArg entry (h j i k)

/-- The literal published factor pair generates its full matrix algebra. -/
theorem full (Q : Subalgebra F (Matrix (Fin (degree 7)) (Fin (degree 7)) F))
    (hQ : ∀ j, factorMatrix 7 j ∈ Q) : Q = ⊤ := by
  have hA : ∀ j, matrix (generators j) ∈ Q := fun j => (generators_eq j).symm ▸ hQ j
  exact full_of_orbits Q generators hA cols rows ci ri cp rp ca ra
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (rankOne_mem Q hA)

end Factor7

namespace Factor8

private def generators : Fin 2 → MatCodes 3 :=
  ![![![0,0,1],
    ![1,0,1],
    ![0,1,1]],
    ![![1,1,0],
    ![0,2,1],
    ![0,0,3]]]

private def cols : MatCodes 3 :=
  ![![1,0,1],
    ![1,1,3],
    ![3,2,2]]

private def rows : MatCodes 3 :=
  ![![1,1,1],
    ![1,3,2],
    ![3,2,0]]

private def ci : MatCodes 3 :=
  ![![2,1,3],
    ![0,3,1],
    ![3,1,3]]

private def ri : MatCodes 3 :=
  ![![2,1,3],
    ![3,2,2],
    ![0,3,1]]

private def cp : Fin 2 → Fin 3 := ![0,1]
private def ca : Fin 2 → Fin 2 := ![1,0]
private def rp : Fin 2 → Fin 3 := ![0,1]
private def ra : Fin 2 → Fin 2 := ![1,0]

private theorem rankOne_mem (Q : Subalgebra F (Matrix (Fin 3) (Fin 3) F))
    (hA : ∀ j, matrix (generators j) ∈ Q) :
    matrix (rankOne (cols 0) (rows 0)) ∈ Q := by
  have hn := plus_scalar_mem Q (generators 0) 1 (hA 0)
  exact product_mem Q _ _ _ hn hn (by decide +kernel)

private theorem generators_eq (j : Fin 2) :
    matrix (generators j) = factorMatrix 8 j := by
  have h : ∀ (j : Fin 2) (i k : Fin 3), generators j i k =
      adaptedRows j (blockIndex 8 i) (blockIndex 8 k) := by decide +kernel
  funext i k
  exact congrArg entry (h j i k)

/-- The literal published factor pair generates its full matrix algebra. -/
theorem full (Q : Subalgebra F (Matrix (Fin (degree 8)) (Fin (degree 8)) F))
    (hQ : ∀ j, factorMatrix 8 j ∈ Q) : Q = ⊤ := by
  have hA : ∀ j, matrix (generators j) ∈ Q := fun j => (generators_eq j).symm ▸ hQ j
  exact full_of_orbits Q generators hA cols rows ci ri cp rp ca ra
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (rankOne_mem Q hA)

end Factor8

end Representation.Hexacode.TwelveDimensional.CosetCertificate.Spanning
