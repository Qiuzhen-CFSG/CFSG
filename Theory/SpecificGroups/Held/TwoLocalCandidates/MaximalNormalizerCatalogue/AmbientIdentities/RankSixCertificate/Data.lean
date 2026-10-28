module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.RankFourKernel.Data
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.TablesSupport

/-!
# The fixed sextets of the two elementary order-64 Held rows

We keep the literal catalogue words and evaluate them through the already
certified representative-generator tables. The common fixed points of the six
generators are checked on all 2058 vertices. Closure then identifies the fixed
points of the actual ambient subgroup, rather than of an abstract replacement.

Source: the ATLAS HeG1-p2058B0 carrier, the catalogue's `source/discovery.json`,
and the two E64.(3.S6) classes in GLS3 Table 5.3p.
-/

public section
namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankSixCertificate
open Subgroup

@[expose] def row (k : Fin 2) : Fin 22 := if k = 0 then 20 else 21

@[expose] def genWord (k : Fin 2) (i : Fin 6) : List ℤ :=
  ((generatorWords (row k))[i.val]?).getD []

@[expose] def gen (k : Fin 2) (i : Fin 6) : He := word (genWord k i)

@[expose] def perm (k : Fin 2) (i : Fin 6) : Equiv.Perm (Fin 2058) :=
  RankFourKernel.tableWord (genWord k i)

theorem perm_eq (k : Fin 2) (i : Fin 6) : perm k i = representation (gen k i) :=
  RankFourKernel.tableWord_eq _

theorem words_row (k : Fin 2) : generatorWords (row k) = List.ofFn (genWord k) := by
  have h : ∀ k : Fin 2, generatorWords (row k) = List.ofFn (genWord k) := by
    decide +kernel
  exact h k

theorem ambient_eq_closure (k : Fin 2) :
    ambient (row k) = closure (Set.range (gen k)) := by
  rw [ambient, entry, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    rw [words_row] at hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨word (genWord k i), ⟨genWord k i, by
      rw [words_row]; exact List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩, rfl⟩

theorem gen_mem (k : Fin 2) (i : Fin 6) : gen k i ∈ ambient (row k) := by
  rw [ambient_eq_closure]
  exact subset_closure (Set.mem_range_self i)

/-- The two actual fixed-point sets, in the original vertex coordinates. -/
@[expose] def sextet (k : Fin 2) : Finset (Fin 2058) :=
  if k = 0 then {480, 944, 1444, 1672, 1877, 1937}
  else {480, 557, 719, 892, 1016, 1444}

set_option maxRecDepth 8192 in
private theorem fixed_check (k : Fin 2) : ∀ x : Fin 2058,
    (∀ i : Fin 6, perm k i x = x) ↔ x ∈ sextet k := by
  fin_cases k <;> apply Cores.allLetters <;> decide +kernel

/-- Identification of the fixed points of each literal word-defined row. -/
theorem fixedPoints_eq (k : Fin 2) :
    MulAction.fixedPoints (ambient (row k)) (Fin 2058) = (sextet k : Set (Fin 2058)) := by
  ext x
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro hx
    exact (fixed_check k x).mp fun i => by
      rw [perm_eq]
      exact hx ⟨gen k i, gen_mem k i⟩
  · intro hx g
    have hle : ambient (row k) ≤ MulAction.stabilizer He x := by
      rw [ambient_eq_closure]
      apply (closure_le _).mpr
      rintro _ ⟨i, rfl⟩
      change representation (gen k i) x = x
      rw [← perm_eq]
      exact (fixed_check k x).mpr hx i
    exact hle g.property

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankSixCertificate
