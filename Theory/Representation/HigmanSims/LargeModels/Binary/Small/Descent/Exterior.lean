module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.Sections
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The actual HS exterior square in the published coordinates

The literal pairs `(j,k)`, ordered first by j and then k with k<j, enumerate
an exterior basis of the degree-twenty space. Their triangular index verifies
the enumeration. Functoriality of exterior powers gives the carrier action;
the two-by-two determinant formula identifies its matrices with
`Small.exteriorMatrix`, including both marked generators.

Source: ATLAS HSG1-f2r20B0 and the exterior sections documented in
`Binary/source/README.md`. In characteristic two the increasing exterior
basis `(k,j)` gives exactly the published `(j,k)` minor formula.
-/

@[expose] public section
open scoped TensorProduct
namespace Representation.HigmanSims.LargeModels.Binary.Small.Descent
open Sporadic.LeechRelated.HS
noncomputable section

abbrev ExteriorSpace := ⋀[ZMod 2]^2 Twenty.Vector

def frame (i : Fin 190) : Fin 2 ↪o Fin 20 :=
  OrderEmbedding.ofStrictMono ![(exteriorPair i).2, (exteriorPair i).1]
    (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [exteriorPair_lt])

def index (i : Fin 190) : Set.powersetCard (Fin 20) 2 :=
  Set.powersetCard.ofFinEmbEquiv (frame i)

private theorem pair_number (i : Fin 190) :
    (exteriorPair i).1.val * ((exteriorPair i).1.val - 1) / 2 +
      (exteriorPair i).2.val = i.val := by
  have h : ∀ i : Fin 190,
      (exteriorPair i).1.val * ((exteriorPair i).1.val - 1) / 2 +
        (exteriorPair i).2.val = i.val := by decide +kernel
  exact h i

theorem exteriorPair_injective : Function.Injective exteriorPair := by
  intro i j h
  apply Fin.ext
  rw [← pair_number i, ← pair_number j, h]

set_option maxRecDepth 1000 in
theorem index_bijective : Function.Bijective index := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro i j h
    apply exteriorPair_injective
    have hf : frame i = frame j := Set.powersetCard.ofFinEmbEquiv.injective h
    apply Prod.ext
    · exact congrArg (fun f : Fin 2 ↪o Fin 20 => f 1) hf
    · exact congrArg (fun f : Fin 2 ↪o Fin 20 => f 0) hf
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Set.powersetCard.card]
    simp only [Nat.card_fin]
    decide

def indexEquiv : Fin 190 ≃ Set.powersetCard (Fin 20) 2 :=
  Equiv.ofBijective index index_bijective

def exteriorBasis : Module.Basis (Fin 190) (ZMod 2) ExteriorSpace :=
  ((Pi.basisFun (ZMod 2) (Fin 20)).exteriorPower 2).reindex indexEquiv.symm

def exteriorAction (C : Twenty.MarkedComparison) :
    Representation (ZMod 2) Carrier ExteriorSpace where
  toFun g := exteriorPower.map 2 (C.action g)
  map_one' := (congrArg (exteriorPower.map 2) C.action.map_one).trans exteriorPower.map_id
  map_mul' g h := (congrArg (exteriorPower.map 2) (C.action.map_mul g h)).trans
    (exteriorPower.map_comp _ _)

private theorem action_apply (C : Twenty.MarkedComparison) (g : Carrier) (v : Twenty.Vector) :
    C.action g v = (Twenty.toMatrix (C.hom g)).mulVec v := rfl

set_option maxRecDepth 1000 in
private theorem frame_zero (i : Fin 190) : frame i 0 = (exteriorPair i).2 := rfl
set_option maxRecDepth 1000 in
private theorem frame_one (i : Fin 190) : frame i 1 = (exteriorPair i).1 := rfl

theorem toMatrix_exteriorAction (C : Twenty.MarkedComparison) (g : Carrier) :
    LinearMap.toMatrix exteriorBasis exteriorBasis (exteriorAction C g) =
      exteriorMatrix (Twenty.toMatrix (C.hom g)) := by
  ext s t
  simp only [LinearMap.toMatrix_apply, exteriorBasis, Module.Basis.reindex_apply,
    Module.Basis.repr_reindex, Equiv.symm_symm, Finsupp.mapDomain_equiv_apply,
    exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorAction, MonoidHom.coe_mk, OneHom.coe_mk,
    exteriorPower.map_apply_ιMulti, exteriorPower.ιMultiDual_apply_ιMulti,
    Module.Basis.coord_apply, Pi.basisFun_repr]
  change (Matrix.of fun a b : Fin 2 =>
    (C.action g) ((Pi.basisFun (ZMod 2) (Fin 20))
      (Set.powersetCard.ofFinEmbEquiv.symm (indexEquiv t) a))
      (Set.powersetCard.ofFinEmbEquiv.symm (indexEquiv s) b)).det = _
  have hindex (u : Fin 190) :
      Set.powersetCard.ofFinEmbEquiv.symm (indexEquiv u) = frame u :=
    Set.powersetCard.ofFinEmbEquiv.symm_apply_apply _
  simp only [hindex]
  simp only [action_apply, Pi.basisFun_apply, Matrix.mulVec_single,
    MulOpposite.op_one, one_smul, Matrix.col_apply,
    Matrix.det_fin_two, Matrix.of_apply, frame_zero, frame_one, CharTwo.sub_eq_add]
  rw [mul_comm (Twenty.toMatrix (C.hom g) (exteriorPair s).2 (exteriorPair t).2)]
  rfl

def ambientHom (C : Twenty.MarkedComparison) :
    Carrier →* Matrix (Fin 190) (Fin 190) (ZMod 2) :=
  (LinearMap.toMatrixAlgEquiv exteriorBasis).toAlgHom.toMonoidHom.comp (exteriorAction C)

theorem ambientHom_apply (C : Twenty.MarkedComparison) (g : Carrier) :
    ambientHom C g = exteriorMatrix (Twenty.toMatrix (C.hom g)) :=
  toMatrix_exteriorAction C g

theorem ambientHom_a (C : Twenty.MarkedComparison) :
    ambientHom C permutationA = ambientGenerator 0 := by
  rw [ambientHom_apply]
  change exteriorMatrix (Twenty.toMatrix (C.hom Twenty.permutationA)) = _
  rw [C.map_a]
  rfl

theorem ambientHom_b (C : Twenty.MarkedComparison) :
    ambientHom C permutationB = ambientGenerator 1 := by
  rw [ambientHom_apply]
  change exteriorMatrix (Twenty.toMatrix (C.hom Twenty.permutationB)) = _
  rw [C.map_b]
  rfl

end
end Representation.HigmanSims.LargeModels.Binary.Small.Descent
