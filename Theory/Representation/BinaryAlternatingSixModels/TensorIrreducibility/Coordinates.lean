module
public import Theory.Representation.BinaryAlternatingSixModels.TensorSplitting
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Theory.Representation.BinaryAlternatingSixModels.TensorIrreducibility.Certificate
/-!
# The checked matrices are the actual alternating tensor action

The coordinate map uses the published polar basis in both tensor factors.
Six pentad identities certify each exceptional-automorphism image. Duad
transport identifies all generator columns, and bilinearity gives the
matrix action on every tensor. Both the original action and its exceptional
twist are retained. Source: Aschbacher–Smith G.5.1, printed pp.342–343.
-/
@[expose] public section
open Theory.SpecificGroups.SymmetricSix BinaryAlternatingSix TensorSplitting
open scoped TensorProduct
namespace BinaryAlternatingSix.TensorIrreducibility.Native
abbrev Vec := Fin 16 → ZMod 2
abbrev Mat := Matrix (Fin 16) (Fin 16) (ZMod 2)
noncomputable def coords : TensorModule ≃ₗ[ZMod 2] Vec :=
  (tensorBasis.reindex finProdFinEquiv).equivFun
theorem coords_basis (i j : Fin 4) :
    coords (tensorBasis (i,j)) = Pi.single (finProdFinEquiv (i,j)) 1 := by
  have he : tensorBasis (i,j) = (tensorBasis.reindex finProdFinEquiv) (finProdFinEquiv (i,j)) := by
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  rw [he]
  ext k
  rw [coords, Module.Basis.equivFun_self]
  simp [Pi.single_apply, eq_comm]

def rPerm : S6 := Equiv.swap 0 1 * (Equiv.swap 2 4 * Equiv.swap 4 3 * Equiv.swap 3 5)
def sPerm : S6 := Equiv.swap 0 1 * Equiv.swap 2 3
def gPerm : S6 := Equiv.swap 0 1 * Equiv.swap 1 2
def hPerm : S6 := Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5
def r : A6 := ⟨rPerm, by decide +kernel⟩
def s : A6 := ⟨sPerm, by decide +kernel⟩
def g : A6 := ⟨gPerm, by decide +kernel⟩
def h : A6 := ⟨hPerm, by decide +kernel⟩
theorem r_mem : r ∈ a6Borel := by decide +kernel
theorem s_mem : s ∈ a6Borel := by decide +kernel

def sOuter : S6 := Equiv.swap 2 4 * Equiv.swap 3 5
def gOuter : S6 := (Equiv.swap 0 4 * Equiv.swap 4 3) * (Equiv.swap 1 2 * Equiv.swap 2 5)
def hOuter : S6 := Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 3 * Equiv.swap 3 1

private theorem diagram_eq_of_pentads (a b : S6)
    (hb : ∀ i : Fin 6, GLS3.Chapter5.pentadAt (align⁻¹ (b (align i))) =
      GLS3.Chapter5.pentadMap a (GLS3.Chapter5.pentadAt i)) : diagramAut a = b := by
  have ho : GLS3.Chapter5.outerHom a = align⁻¹ * b * align := by
    apply Equiv.ext
    intro i
    apply GLS3.Chapter5.pentadAt_injective
    exact (GLS3.Chapter5.outerAct_spec a i).trans (hb i).symm
  change align * GLS3.Chapter5.outerHom a * align⁻¹ = b
  rw [ho]
  group

theorem diagram_r : diagramAut rPerm = rPerm := by
  apply diagram_eq_of_pentads
  intro i
  fin_cases i <;> decide +kernel

theorem diagram_s : diagramAut sPerm = sOuter := by
  apply diagram_eq_of_pentads
  intro i
  fin_cases i <;> decide +kernel

theorem diagram_g : diagramAut gPerm = gOuter := by
  apply diagram_eq_of_pentads
  intro i
  fin_cases i <;> decide +kernel

theorem diagram_h : diagramAut hPerm = hOuter := by
  apply diagram_eq_of_pentads
  intro i
  fin_cases i <;> decide +kernel

end BinaryAlternatingSix.TensorIrreducibility.Native

namespace BinaryAlternatingSix.TensorIrreducibility.Native
open BinaryAlternatingSix.TensorIrreducibility.Certificate
def slot : Fin 4 → Fin 2 ⊕ Fin 2 := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1]
def readNatural : NaturalModule →ₗ[ZMod 2] (Fin 4 → ZMod 2) where
  toFun v i := v (slot i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem natural_coordinate (v : NaturalModule) (i : Fin 4) : naturalBasis.repr v i = v (slot i) := by
  have he : naturalBasis.equivFun.toLinearMap = readNatural := by
    apply naturalBasis.ext
    intro j
    ext k
    change naturalBasis.equivFun (naturalBasis j) k = _
    rw [Module.Basis.equivFun_self]
    rw [naturalBasis_apply]
    fin_cases j <;> fin_cases k <;> decide +kernel
  exact congrFun (LinearMap.congr_fun he v) i

theorem coords_tmul (v w : NaturalModule) (k : Fin 16) :
    coords (v ⊗ₜ[ZMod 2] w) k =
      v (slot ((finProdFinEquiv (m := 4) (n := 4)).symm k).1) * w (slot ((finProdFinEquiv (m := 4) (n := 4)).symm k).2) := by
  change (tensorBasis.reindex finProdFinEquiv).repr (v ⊗ₜ[ZMod 2] w) k = _
  rw [Module.Basis.repr_reindex_apply, Module.Basis.tensorProduct_repr_tmul_apply,
    natural_coordinate, natural_coordinate]
  exact mul_comm _ _

def actor : Fin 4 → A6 := ![r,s,g,h]
def outer : Fin 4 → S6 := ![rPerm,sOuter,gOuter,hOuter]
def matrix : Fin 4 → BinaryAlternatingSix.TensorIrreducibility.Certificate.Mat := ![R,S,G,H]
def basisDuad : Fin 4 → Duad := ![13,1,14,0]
def firstDuad : Fin 4 → Fin 4 → Duad := ![![11, 7, 9, 0], ![11, 6, 14, 0], ![13, 0, 14, 5], ![7, 2, 8, 1]]
def secondDuad : Fin 4 → Fin 4 → Duad := ![![11, 7, 9, 0], ![13, 3, 9, 0], ![0, 14, 6, 10], ![8, 10, 13, 1]]

theorem actor_outer (a : Fin 4) : diagramAut (actor a).val = outer a := by
  fin_cases a
  · exact diagram_r
  · exact diagram_s
  · exact diagram_g
  · exact diagram_h

theorem naturalBasis_polar (i : Fin 4) : naturalBasis i = (polarVector (basisDuad i)).val := by
  rw [naturalBasis_apply]
  fin_cases i <;> rfl

theorem actor_first (a i : Fin 4) :
    firstAlternating (actor a) (naturalBasis i) = (polarVector (firstDuad a i)).val := by
  change polarAction (actor a).val (naturalBasis i) = _
  rw [naturalBasis_polar, polarAction_vector]
  congr 2
  apply duadSet_injective
  rw [duadSet_smul]
  fin_cases a <;> fin_cases i <;> decide +kernel

theorem actor_second (a i : Fin 4) :
    secondAlternating (actor a) (naturalBasis i) = (polarVector (secondDuad a i)).val := by
  change polarAction (diagramAut (actor a).val) (naturalBasis i) = _
  rw [actor_outer, naturalBasis_polar, polarAction_vector]
  congr 2
  apply duadSet_injective
  rw [duadSet_smul]
  fin_cases a <;> fin_cases i <;> decide +kernel

theorem matrix_basis (a i j : Fin 4) :
    coords (alternatingTensor (actor a) (tensorBasis (i,j))) =
      (matrix a).mulVec (coords (tensorBasis (i,j))) := by
  rw [alternatingTensor_tensorBasis_apply, actor_first, actor_second, coords_basis]
  ext k
  rw [coords_tmul, Matrix.mulVec_single, MulOpposite.op_one, one_smul]
  fin_cases a <;> fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

theorem matrix_action (a : Fin 4) (v : TensorModule) :
    coords (alternatingTensor (actor a) v) = (matrix a).mulVec (coords v) := by
  have he : coords.toLinearMap.comp (alternatingTensor (actor a)) =
      (Matrix.toLin' (matrix a)).comp coords.toLinearMap := by
    apply tensorBasis.ext
    intro ij
    exact matrix_basis a ij.1 ij.2
  exact LinearMap.congr_fun he v
end BinaryAlternatingSix.TensorIrreducibility.Native
