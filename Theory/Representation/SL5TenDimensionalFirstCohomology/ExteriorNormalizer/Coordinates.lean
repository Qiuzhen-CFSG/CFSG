module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Models
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.FinCases

/-!
# Coordinates for the two ten-dimensional exterior actions

The increasing pairs and triples give bases of the literal exterior powers of
F₂⁵. In these bases the action consists of determinant minors. These coordinates
are used to compute the commuting algebra and to distinguish the graph twist.

Source application: Aschbacher--Smith, G.9.3(13), printed pp.354, 356--357.
The minor calculation follows `ExteriorVanishing.Reduction`, independently of
its cohomology results.
-/

@[expose] public section
namespace Representation.SL5TenDimensional.ExteriorNormalizer
open scoped BigOperators

/-- The two exterior degrees. -/
def degree : Fin 2 → ℕ := ![2, 3]

/-- The increasing coordinate frames, in lexicographic order. -/
def frame : (a : Fin 2) → Fin 10 → Fin (degree a) ↪o Fin 5 :=
  Fin.cases (fun s => OrderEmbedding.ofStrictMono
    (![![0,1], ![0,2], ![0,3], ![0,4], ![1,2], ![1,3], ![1,4], ![2,3], ![2,4], ![3,4]] s)
    (by change StrictMono (show Fin 2 → Fin 5 from _); revert s; decide))
  (Fin.cases (fun s => OrderEmbedding.ofStrictMono
    (![![0,1,2], ![0,1,3], ![0,1,4], ![0,2,3], ![0,2,4], ![0,3,4],
      ![1,2,3], ![1,2,4], ![1,3,4], ![2,3,4]] s)
    (by change StrictMono (show Fin 3 → Fin 5 from _); revert s; decide)) (fun a => Fin.elim0 a))

/-- Enumeration of exterior-basis indices. -/
def index (a : Fin 2) (s : Fin 10) : Set.powersetCard (Fin 5) (degree a) :=
  Set.powersetCard.ofFinEmbEquiv (frame a s)

set_option maxRecDepth 10000 in
theorem index_bijective (a : Fin 2) : Function.Bijective (index a) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · fin_cases a <;> decide +kernel
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Set.powersetCard.card]
    simp only [Nat.card_fin]
    fin_cases a <;> decide

/-- Reindexing the exterior basis by ten coordinates. -/
noncomputable def indexEquiv (a : Fin 2) : Fin 10 ≃ Set.powersetCard (Fin 5) (degree a) :=
  Equiv.ofBijective (index a) (index_bijective a)

/-- The standard exterior basis with ten coordinates. -/
noncomputable def basis (a : Fin 2) :
    Module.Basis (Fin 10) (ZMod 2) (ExteriorModule (degree a)) :=
  ((Pi.basisFun (ZMod 2) (Fin 5)).exteriorPower (degree a)).reindex (indexEquiv a).symm

/-- The matrix of determinant minors. -/
def actionMatrix (a : Fin 2) (g : Group) : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  fun s t => (Matrix.of fun b c : Fin (degree a) => g.val (frame a s c) (frame a t b)).det

/-- The minor matrix represents the literal exterior action. -/
theorem toMatrix_action (a : Fin 2) (g : Group) :
    LinearMap.toMatrix (basis a) (basis a) (exteriorAction (degree a) g) =
      actionMatrix a g := by
  ext s t
  simp only [LinearMap.toMatrix_apply, basis, Module.Basis.reindex_apply,
    Module.Basis.repr_reindex, Equiv.symm_symm, Finsupp.mapDomain_equiv_apply,
    exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorAction_ιMulti,
    exteriorPower.ιMultiDual_apply_ιMulti, Module.Basis.coord_apply,
    Pi.basisFun_repr, Pi.basisFun_apply, Function.comp_apply,
    Matrix.mulVec_single, actionMatrix]
  simp [indexEquiv, index]

/-- Compute the trace using the ten determinant coordinates. -/
theorem trace_action (a : Fin 2) (g : Group) :
    LinearMap.trace (ZMod 2) (ExteriorModule (degree a)) (exteriorAction (degree a) g) =
      (actionMatrix a g).trace := by
  rw [LinearMap.trace_eq_matrix_trace (ZMod 2) (basis a), toMatrix_action]

end Representation.SL5TenDimensional.ExteriorNormalizer
