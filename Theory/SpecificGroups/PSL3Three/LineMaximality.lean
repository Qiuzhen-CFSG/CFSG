module

public import Theory.SpecificGroups.PSL3Three.CandidateCertificate

/-!
# Maximality of the lineStabilizerSL matrix subgroup

A kernel-checked right-coset table has 13 rows. It reduces to
2 double cosets; each nonidentity double coset has explicit words
recovering the ambient generators after adjoining its representative.
The subgroup generators satisfy the membership test for the actual subgroup
in `Subgroups`, so the tables prove maximality of that concrete candidate.

Source: GLS III, Theorem 6.5.3(a–c). The data below are witnesses only;
`isCoatom_of_matrixCertificate` checks their mathematical sufficiency.
-/

namespace Matrix.PSL3Three
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def gen : Fin 4 → SL :=
  ![⟨!![2, 1, 0; 0, 0, 1; 0, 1, 2], by decide⟩,
    ⟨!![1, 1, 0; 0, 2, 1; 0, 2, 0], by decide⟩,
    ⟨!![2, 1, 1; 0, 1, 1; 0, 1, 0], by decide⟩,
    ⟨!![1, 0, 1; 0, 0, 2; 0, 1, 2], by decide⟩]

private def inverse : Fin 4 → Fin 4 := ![2,
    3,
    0,
    1]

private theorem hinverse (i : Fin 4) : gen (inverse i) = (gen i)⁻¹ := by
  apply Subtype.ext
  revert i
  decide

private theorem hgen (i : Fin 4) : gen i ∈ lineStabilizerSL := by
  rw [mem_lineStabilizerSL_iff]
  revert i
  decide

private def rep : Fin 13 → SL :=
  ![⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], by decide⟩,
    ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩,
    ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide⟩,
    ⟨!![0, 1, 0; 0, 0, 1; 1, 1, 0], by decide⟩,
    ⟨!![0, 1, 0; 0, 0, 1; 1, 2, 0], by decide⟩,
    ⟨!![1, 0, 0; 0, 1, 0; 1, 0, 1], by decide⟩,
    ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 1], by decide⟩,
    ⟨!![1, 0, 0; 0, 1, 0; 2, 0, 1], by decide⟩,
    ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 2], by decide⟩,
    ⟨!![0, 0, 1; 1, 1, 0; 0, 1, 1], by decide⟩,
    ⟨!![0, 0, 1; 1, 2, 0; 0, 1, 1], by decide⟩,
    ⟨!![0, 0, 1; 1, 1, 0; 0, 1, 2], by decide⟩,
    ⟨!![0, 0, 1; 1, 2, 0; 0, 1, 2], by decide⟩]

private def table : RightCosetTable 4 4 13 where
  base := 0
  next := ![![1,
    0,
    2,
    0],
    ![2,
    1,
    0,
    1],
    ![0,
    3,
    1,
    4],
    ![5,
    4,
    6,
    2],
    ![7,
    2,
    8,
    3],
    ![6,
    5,
    3,
    5],
    ![3,
    9,
    5,
    10],
    ![8,
    7,
    4,
    7],
    ![4,
    11,
    7,
    12],
    ![11,
    10,
    10,
    6],
    ![9,
    6,
    11,
    9],
    ![10,
    12,
    9,
    8],
    ![12,
    8,
    12,
    11]]
  factor := ![![[],
    [0, 1, 0, 1],
    [],
    [3, 2, 3, 2]],
    ![[],
    [3, 0, 0, 3],
    [],
    [1, 2, 2, 1]],
    ![[],
    [],
    [],
    []],
    ![[],
    [],
    [],
    []],
    ![[],
    [],
    [],
    []],
    ![[],
    [0, 3, 0, 0, 3, 2],
    [],
    [0, 0, 3, 0, 0, 3]],
    ![[],
    [],
    [],
    []],
    ![[],
    [0, 1, 0, 3, 0, 0],
    [],
    [0, 3, 0, 0, 0, 1]],
    ![[],
    [],
    [],
    []],
    ![[2, 3, 0, 0, 0],
    [],
    [3, 2, 2, 2, 1],
    []],
    ![[3, 0, 0, 0, 1],
    [],
    [3, 2, 3],
    []],
    ![[1, 0, 1],
    [],
    [2, 2, 2, 1, 0],
    []],
    ![[3, 2, 1, 0, 1],
    [],
    [3, 2, 3, 0, 1],
    []]]

private theorem htable : table.Valid ambientGenerators gen rep := by
  constructor
  · decide
  · intro a i
    apply Subtype.ext
    revert a i
    decide

private def doubleRep : Fin 2 → SL :=
  ![⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], by decide⟩,
    ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩]

private def index : Fin 13 → Fin 2 :=
  ![0,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1]

private def left : Fin 13 → List (Fin 4) :=
  ![[],
    [],
    [2, 1, 0, 0],
    [2, 1, 0, 0],
    [2, 1, 0, 0],
    [3, 2, 2, 2, 1],
    [],
    [2, 2, 2, 1, 0],
    [],
    [],
    [],
    [],
    []]

private def right : Fin 13 → List (Fin 4) :=
  ![[],
    [],
    [3, 0, 0, 0, 0],
    [0, 0, 0, 0, 3],
    [2, 3, 0, 0, 3, 2],
    [3, 0, 1, 0, 3],
    [3, 0, 0, 3],
    [1, 2, 3, 2, 1],
    [1, 2, 2, 1],
    [1, 2, 3, 0, 3],
    [0, 0, 1, 2, 2],
    [3, 0, 3, 0, 3],
    [1, 2, 2, 2, 3, 2]]

private theorem hdouble (a : Fin 13) :
    rep a = evalWord gen (left a) * doubleRep (index a) * evalWord gen (right a) := by
  apply Subtype.ext
  revert a
  decide

private def extension : Fin 2 → Fin 4 → List (Fin (4 + 2)) :=
  ![![[],
    [],
    [],
    []],
    ![[4],
    [0, 1, 0, 1],
    [5],
    [3, 2, 3, 2]]]

private theorem hextension (a : Fin 2) :
    doubleRep a ∈ lineStabilizerSL ∨ ∀ i,
      evalWord (extensionGen gen (doubleRep a)) (extension a i) = ambientGenerators i := by
  fin_cases a
  · left
    change doubleRep 0 ∈ lineStabilizerSL
    rw [show doubleRep 0 = 1 by decide]
    exact Subgroup.one_mem _
  · right
    intro i
    apply Subtype.ext
    revert i
    decide

/-- The specified lineStabilizerSL is a proper subgroup. -/
public theorem lineStabilizerSL_ne_top : lineStabilizerSL ≠ ⊤ := by
  have h : ambientGenerators 0 ∉ lineStabilizerSL := by
    rw [mem_lineStabilizerSL_iff]
    decide
  intro heq
  exact h (heq.symm ▸ Subgroup.mem_top _)

/-- The concrete lineStabilizerSL is maximal in SL₃(3). -/
public theorem isCoatom_lineStabilizerSL : IsCoatom lineStabilizerSL :=
  isCoatom_of_matrixCertificate lineStabilizerSL lineStabilizerSL_ne_top
    gen inverse hinverse hgen rep table htable doubleRep index left right hdouble
    extension hextension

end Matrix.PSL3Three
