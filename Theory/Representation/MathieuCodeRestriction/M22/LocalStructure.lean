module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Trio
public import Theory.PGroupCore


/-!
# Geometry compatible with the native M22 pair

The standard sextet separates coordinates 0 and 9. Conjugating by the certified
native word `aba` gives a sextet with first tetrad `{0,2,9,14}`. All six tetrads,
the incident octad, and the trio are explicit; their source partition properties
are kernel-checked, and their equality with the corresponding translates is
proved. This fixes the coordinate compatibility required by H.14--H.16.

The inner and outer hexad and quintet stabilizers are literal preimages of
these geometry stabilizers. Their kernels are intrinsic two-cores, mapped back
into the appropriate ambient group; no ambient normality or local structure
is built into the definitions. A common Sylow arrangement remains a group
structure theorem, not a consequence of incidence alone.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), setup of H.14,
printed p.396 (PDF p.407), with H.15.4--5 and H.16.3--4.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open scoped Pointwise
namespace MathieuCode

/-- The short native M24 word carrying the standard first tetrad onto
`{0,2,9,14}`, which contains both distinguished coordinates. -/
def m22GeometryConjugator : M24 :=
  ⟨m24GeneratorA * m24GeneratorB * m24GeneratorA,
    M24.mul_mem (M24.mul_mem m24GeneratorA_mem m24GeneratorB_mem) m24GeneratorA_mem⟩

/-- Tetrads in a sextet compatible with the native fixed pair. -/
def m22SourceTetrad : Fin 6 → Finset (Fin 24)
  | 0 => {0, 2, 9, 14}
  | 1 => {7, 10, 20, 23}
  | 2 => {12, 15, 16, 22}
  | 3 => {4, 5, 8, 13}
  | 4 => {1, 3, 6, 19}
  | 5 => {11, 17, 18, 21}

theorem m22SourceTetrad_eq_smul (i : Fin 6) :
    m22SourceTetrad i = m22GeometryConjugator • standardTetrad i := by
  fin_cases i <;> decide +kernel

theorem m22SourceTetrad_union_octad (i j : Fin 6) (hij : i ≠ j) :
    m22SourceTetrad i ∪ m22SourceTetrad j ∈ m24Blocks := by
  rw [m22SourceTetrad_eq_smul, m22SourceTetrad_eq_smul, ← Finset.smul_finset_union]
  have hg := (mem_M24_iff _).mp m22GeometryConjugator.property
  change m22GeometryConjugator.val • (standardTetrad i ∪ standardTetrad j) ∈
    (m24Blocks : Set (Finset (Fin 24)))
  rw [← hg]
  exact Set.smul_mem_smul_set (standardTetrad_union_mem i j hij)

def m22SourceSextet : Sextet where
  parts := Finset.univ.image m22SourceTetrad
  card := by decide +kernel
  tetrad A hA := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    fin_cases i <;> decide +kernel
  disjoint A hA B hB hne := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
    fin_cases i <;> fin_cases j <;>
      first | exact (hne rfl).elim | decide +kernel
  cover := by decide +kernel
  octad A hA B hB hne := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
    exact m22SourceTetrad_union_octad i j (fun h => hne (congrArg m22SourceTetrad h))

def m22SourceOctad : Octad :=
  ⟨m22SourceTetrad 0 ∪ m22SourceTetrad 1, m22SourceTetrad_union_octad 0 1 (by decide)⟩

def m22SourceTrioOctad : Fin 3 → Finset (Fin 24)
  | 0 => m22SourceTetrad 0 ∪ m22SourceTetrad 1
  | 1 => m22SourceTetrad 2 ∪ m22SourceTetrad 3
  | 2 => m22SourceTetrad 4 ∪ m22SourceTetrad 5

def m22SourceTrio : Trio where
  parts := Finset.univ.image m22SourceTrioOctad
  card := by decide +kernel
  octad A hA := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    fin_cases i <;> exact m22SourceTetrad_union_octad _ _ (by decide)
  disjoint A hA B hB hne := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
    fin_cases i <;> fin_cases j <;>
      first | exact (hne rfl).elim | decide +kernel
  cover := by decide +kernel

theorem m22SourceSextet_eq_smul :
    m22SourceSextet.parts = m22GeometryConjugator • standardSextet.parts := by
  decide +kernel

/-- The standard sextet cannot be used with the native M22 pair. -/
theorem m22Pair_not_in_standardTetrad :
    ¬ ∃ B ∈ standardSextet.parts, m22Pair ⊆ B := by decide +kernel

theorem m22SourceOctad_eq_smul :
    m22SourceOctad.val = m22GeometryConjugator • standardOctad.val := by decide +kernel

theorem m22SourceTrio_eq_smul :
    m22SourceTrio.parts = m22GeometryConjugator • standardTrio.parts := by decide +kernel

theorem m22Pair_le_sourceTetrad : m22Pair ⊆ m22SourceTetrad 0 := by decide +kernel

theorem m22Pair_le_sourceOctad : m22Pair ⊆ m22SourceOctad.val := by decide +kernel

theorem m22SourceTetrad_mem : m22SourceTetrad 0 ∈ m22SourceSextet.parts := by decide +kernel

theorem m22SourceOctad_mem_trio : m22SourceOctad.val ∈ m22SourceTrio.parts := by decide +kernel

/-- The hexad stabilizer in the setwise pair group. -/
def m22OuterHexadStabilizer (O : Octad) : Subgroup m22PairStabilizer :=
  (octadStabilizer O).comap m22PairStabilizer.subtype

/-- The quintet stabilizer, for sextets whose distinguished pair lies in one tetrad. -/
def m22OuterQuintetStabilizer (S : Sextet) : Subgroup m22PairStabilizer :=
  (sextetStabilizer S).comap m22PairStabilizer.subtype

/-- The two-core is taken inside the hexad stabilizer and then included. -/
def m22OuterHexadKernel (O : Octad) : Subgroup m22PairStabilizer :=
  (pCore 2 (m22OuterHexadStabilizer O)).map (m22OuterHexadStabilizer O).subtype

/-- The two-core is taken inside the quintet stabilizer and then included. -/
def m22OuterQuintetKernel (S : Sextet) : Subgroup m22PairStabilizer :=
  (pCore 2 (m22OuterQuintetStabilizer S)).map (m22OuterQuintetStabilizer S).subtype

def m22InnerHexadStabilizer (O : Octad) : Subgroup M22 :=
  (octadStabilizer O).comap m22Embedding

def m22InnerQuintetStabilizer (S : Sextet) : Subgroup M22 :=
  (sextetStabilizer S).comap m22Embedding

def m22InnerHexadKernel (O : Octad) : Subgroup M22 :=
  (pCore 2 (m22InnerHexadStabilizer O)).map (m22InnerHexadStabilizer O).subtype

def m22InnerQuintetKernel (S : Sextet) : Subgroup M22 :=
  (pCore 2 (m22InnerQuintetStabilizer S)).map (m22InnerQuintetStabilizer S).subtype

end MathieuCode
