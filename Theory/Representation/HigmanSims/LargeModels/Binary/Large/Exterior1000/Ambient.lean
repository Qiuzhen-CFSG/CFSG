module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Assembly
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FinCases

/-!
# The actual exterior-square(56) action in the ATLAS section coordinates

Apply the exterior-power functor to the supplied action of the literal HS
permutation carrier. The standard exterior basis, reindexed by the triangular
order (j,k), k<j, gives 1540 coordinates. Its matrix is the binary two-by-two
minor formula. The increasing wedge basis uses (k,j); in characteristic two the
two wedge orders agree. Both source generators retain their raw left matrices.

The triangular enumeration is proved structurally using `finSigmaFinEquiv`,
without a quadratic finite injectivity check or a large table of Fin pairs.
The subsequent numerical row certificates use exactly `ambientA` and `ambientB`.

Source: R. A. Wilson et al., ATLAS HSG1-f2r56B0 and HSG1-f2r1000B0,
with the exterior-section convention in `Binary/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000
open Sporadic.LeechRelated.HS

/-- Triangular enumeration, first by the upper coordinate, then the lower. -/
def pairEquiv : (Σ j : Fin 56, Fin j.val) ≃ Fin 1540 :=
  finSigmaFinEquiv.trans (finCongr (by decide +kernel))

def pair (i : Fin 1540) : Fin 56 × Fin 56 :=
  let p := pairEquiv.symm i
  (p.1, ⟨p.2.val, p.2.isLt.trans p.1.isLt⟩)

theorem pair_lt (i : Fin 1540) : (pair i).2 < (pair i).1 :=
  (pairEquiv.symm i).2.isLt

theorem pair_index (i : Fin 1540) :
    (pair i).1.val * ((pair i).1.val - 1) / 2 + (pair i).2.val = i.val := by
  have h := finSigmaFinEquiv_apply (pairEquiv.symm i)
  have hi : (finSigmaFinEquiv (pairEquiv.symm i)).val = i.val :=
    congrArg Fin.val (pairEquiv.apply_symm_apply i)
  rw [hi] at h
  rw [h]
  simp only [pair, Fin.castLE]
  congr 1
  rw [← Finset.sum_range_id, ← Fin.sum_univ_eq_sum_range]

theorem pair_injective : Function.Injective pair := by
  intro i j h
  apply Fin.ext
  rw [← pair_index i, ← pair_index j, h]

def frame (i : Fin 1540) : Fin 2 ↪o Fin 56 :=
  OrderEmbedding.ofStrictMono (![ (pair i).2, (pair i).1 ]) (by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [pair_lt])

def index (i : Fin 1540) : Set.powersetCard (Fin 56) 2 :=
  Set.powersetCard.ofFinEmbEquiv (frame i)

theorem index_injective : Function.Injective index := by
  intro i j h
  have hf : frame i = frame j := Set.powersetCard.ofFinEmbEquiv.injective h
  apply pair_injective
  apply Prod.ext
  · exact congrArg (fun f : Fin 2 ↪o Fin 56 => f 1) hf
  · exact congrArg (fun f : Fin 2 ↪o Fin 56 => f 0) hf

theorem index_bijective : Function.Bijective index := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨index_injective, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Set.powersetCard.card]
  simp only [Nat.card_fin]
  decide

noncomputable def indexEquiv : Fin 1540 ≃ Set.powersetCard (Fin 56) 2 :=
  Equiv.ofBijective index index_bijective

@[simp] theorem indexEquiv_apply (i : Fin 1540) : indexEquiv i = index i := rfl

theorem index_order (i : Fin 1540) :
    Set.powersetCard.ofFinEmbEquiv.symm (index i) = frame i :=
  Set.powersetCard.ofFinEmbEquiv.symm_apply_apply _

abbrev ExteriorSpace := ⋀[ZMod 2]^2 (Fin 56 → ZMod 2)

noncomputable def basis : Module.Basis (Fin 1540) (ZMod 2) ExteriorSpace :=
  ((Pi.basisFun (ZMod 2) (Fin 56)).exteriorPower 2).reindex indexEquiv.symm

/-- Present the supplied action at its literal numerical dimension. -/
def sourceAction (C56 : MarkedAction 0) :
    Representation (ZMod 2) Carrier (Fin 56 → ZMod 2) := C56.action

/-- The literal exterior-power functor applied to the supplied actual HS action. -/
noncomputable def exteriorAction (C56 : MarkedAction 0) :
    Representation (ZMod 2) Carrier ExteriorSpace where
  toFun g := exteriorPower.map 2 (sourceAction C56 g)
  map_one' := by
    rw [map_one]
    exact exteriorPower.map_id
  map_mul' g h := by
    rw [map_mul]
    exact exteriorPower.map_comp (sourceAction C56 h) (sourceAction C56 g)

/-- The same functorial action in the source's 1540 ordered coordinates. -/
noncomputable def ambientAction (C56 : MarkedAction 0) :
    Representation (ZMod 2) Carrier (Fin 1540 → ZMod 2) where
  toFun g := (LinearMap.toMatrix basis basis (exteriorAction C56 g)).mulVecLin
  map_one' := by
    rw [map_one, LinearMap.toMatrix_one, Matrix.mulVecLin_one]
    rfl
  map_mul' g h := by
    rw [map_mul, LinearMap.toMatrix_mul, Matrix.mulVecLin_mul]
    rfl

/-- The coordinate action is transported from the literal exterior functor. -/
theorem ambientAction_coordinates (C56 : MarkedAction 0) (g : Carrier)
    (v : ExteriorSpace) :
    ambientAction C56 g (basis.equivFun v) =
      basis.equivFun (exteriorAction C56 g v) := by
  simp only [ambientAction, MonoidHom.coe_mk, OneHom.coe_mk,
    Matrix.mulVecLin_apply, Module.Basis.equivFun_apply]
  exact LinearMap.toMatrix_mulVec_repr basis basis (exteriorAction C56 g) v

/-- The binary two-by-two minor formula, with the raw left-action convention. -/
def exteriorMatrix (M : Matrix (Fin 56) (Fin 56) (ZMod 2)) :
    Matrix (Fin 1540) (Fin 1540) (ZMod 2) := fun i j =>
  M (pair i).1 (pair j).1 * M (pair i).2 (pair j).2 +
  M (pair i).1 (pair j).2 * M (pair i).2 (pair j).1

theorem toMatrix_exteriorAction (C56 : MarkedAction 0) (g : Carrier) :
    LinearMap.toMatrix basis basis (exteriorAction C56 g) =
      exteriorMatrix (LinearMap.toMatrix' (sourceAction C56 g)) := by
  ext s t
  simp only [LinearMap.toMatrix_apply, basis, Module.Basis.reindex_apply,
    Module.Basis.repr_reindex, Equiv.symm_symm, Finsupp.mapDomain_equiv_apply,
    exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family]
  change exteriorPower.ιMultiDual (ZMod 2) 2 _ (index s)
    (exteriorPower.map 2 (sourceAction C56 g) (exteriorPower.ιMulti (ZMod 2) 2 _)) = _
  rw [exteriorPower.map_apply_ιMulti, exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [indexEquiv_apply, index_order, Matrix.det_fin_two, Matrix.of_apply,
    Function.comp_apply, Module.Basis.coord_apply, Pi.basisFun_repr, Pi.basisFun_apply,
    LinearMap.toMatrix'_apply, exteriorMatrix, CharTwo.sub_eq_add]
  change sourceAction C56 g (Pi.single (pair t).2 1) (pair s).2 *
      sourceAction C56 g (Pi.single (pair t).1 1) (pair s).1 +
      sourceAction C56 g (Pi.single (pair t).2 1) (pair s).1 *
      sourceAction C56 g (Pi.single (pair t).1 1) (pair s).2 = _
  ac_rfl

theorem toMatrix_ambientAction (C56 : MarkedAction 0) (g : Carrier) :
    LinearMap.toMatrix' (ambientAction C56 g) =
      exteriorMatrix (LinearMap.toMatrix' (sourceAction C56 g)) := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  simp only [ambientAction, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  exact congrFun (congrFun (toMatrix_exteriorAction C56 g) i) j

def ambientA : Matrix (Fin 1540) (Fin 1540) (ZMod 2) := exteriorMatrix (aMatrix 0)
def ambientB : Matrix (Fin 1540) (Fin 1540) (ZMod 2) := exteriorMatrix (bMatrix 0)

theorem ambientAction_a (C56 : MarkedAction 0) :
    LinearMap.toMatrix' (ambientAction C56 permutationA) = ambientA := by
  rw [toMatrix_ambientAction]
  exact congrArg exteriorMatrix C56.matrix_a

theorem ambientAction_b (C56 : MarkedAction 0) :
    LinearMap.toMatrix' (ambientAction C56 permutationB) = ambientB := by
  rw [toMatrix_ambientAction]
  exact congrArg exteriorMatrix C56.matrix_b

/-- The raw degree-1000 first generator at its literal numerical dimension. -/
def targetA : Matrix (Fin 1000) (Fin 1000) (ZMod 2) := aMatrix 3

/-- The raw degree-1000 second generator at its literal numerical dimension. -/
def targetB : Matrix (Fin 1000) (Fin 1000) (ZMod 2) := bMatrix 3

theorem targetA_eq : targetA = aMatrix 3 := rfl
theorem targetB_eq : targetB = bMatrix 3 := rfl

end Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000
