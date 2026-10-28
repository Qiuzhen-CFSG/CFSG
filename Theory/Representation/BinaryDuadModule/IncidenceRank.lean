module

public import Theory.Representation.BinaryDuadModule
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Rank of the line-complement incidence span

Nine explicit reduced rows form a basis of the complement incidence span of
the binary symplectic quadrangle. Each reduced row is checked as a sum of
original line complements, and every original line complement is reconstructed
from the reduced rows. Evaluation at the nine pivot coordinates proves linear
independence without enumerating subspaces or all vectors.

The rank-nine result and the natural rank-four embedding give the two
five-dimensional sections used in Aschbacher–Smith G.5.3(3),(5), printed
pp.343–345. Their identification as covers is not asserted here.
-/

public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation
namespace BinaryDuadModule

private def row (n : ℕ) : Full Duad := fun i => if n.testBit i.val then 1 else 0
private def reducedRow (i : Fin 9) : Full Duad :=
  row (![28945, 30738, 20500, 12312, 31008, 20800, 12672, 23040, 15360] i)
private def pivot : Fin 9 → Duad := ![0, 1, 2, 3, 5, 6, 7, 9, 10]
private def combination (i : Fin 9) : ℕ := ![651, 687, 575, 127, 240, 40, 48, 5, 6] i

private theorem reducedRow_pivot (i j : Fin 9) :
    reducedRow j (pivot i) = if j = i then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> decide

private theorem reducedRow_eq_sum (i : Fin 9) :
    reducedRow i = ∑ s ∈ Finset.univ.filter (fun s : Syntheme => (combination i).testBit s.val),
      lineComplement s := by
  fin_cases i <;> decide

private theorem lineComplement_eq_sum (s : Syntheme) :
    lineComplement s = ∑ i : Fin 9, lineComplement s (pivot i) • reducedRow i := by
  fin_cases s <;> decide

private theorem reducedRow_span :
    Submodule.span (ZMod 2) (Set.range reducedRow) = lineComplementSpan := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [reducedRow_eq_sum]
    apply Submodule.sum_mem
    intro s _
    exact Submodule.subset_span (Set.mem_range_self s)
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    rw [lineComplement_eq_sum]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

private theorem reducedRow_injective :
    Function.Injective (Fintype.linearCombination (ZMod 2) reducedRow) := by
  have h (v : Fin 9 → ZMod 2) (i : Fin 9) :
      Fintype.linearCombination (ZMod 2) reducedRow v (pivot i) = v i := by
    change (∑ j : Fin 9, v j • reducedRow j) (pivot i) = v i
    simp only [Finset.sum_apply, Pi.smul_apply, reducedRow_pivot]
    simp
  intro v w hvw
  ext i
  exact (h v i).symm.trans ((congrFun hvw (pivot i)).trans (h w i))

/-- The complement incidence matrix of the binary symplectic quadrangle has rank nine.
The proof checks nine reduced rows and their expressions in the original lines. -/
theorem lineComplementSpan_finrank :
    Module.finrank (ZMod 2) lineComplementSpan = 9 := by
  rw [← reducedRow_span, ← Fintype.range_linearCombination,
    LinearMap.finrank_range_of_inj reducedRow_injective]
  simp

/-- The even-weight module modulo the line-complement span has dimension five. -/
theorem core_quotient_lineComplementSpan_finrank :
    Module.finrank (ZMod 2)
      (core Duad ⧸ lineComplementSpan.comap (core Duad).subtype) = 5 := by
  have h := (lineComplementSpan.comap (core Duad).subtype).finrank_quotient_add_finrank
  rw [(Submodule.comapSubtypeEquivOfLe lineComplementSpan_le_core).finrank_eq,
    lineComplementSpan_finrank, finrank_core] at h
  norm_num at h
  omega

/-- The line-complement span modulo the embedded natural module has dimension five. -/
theorem lineComplementSpan_quotient_complement_finrank :
    Module.finrank (ZMod 2) (lineComplementSpan ⧸
      complementSubrepresentation.toSubmodule.comap lineComplementSpan.subtype) = 5 := by
  have h := (complementSubrepresentation.toSubmodule.comap
    lineComplementSpan.subtype).finrank_quotient_add_finrank
  rw [(Submodule.comapSubtypeEquivOfLe
    complementSubrepresentation_le_lineComplementSpan).finrank_eq,
    complementSubrepresentation_finrank, lineComplementSpan_finrank] at h
  omega

end BinaryDuadModule
