module
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal.EdgeMarks
public import Theory.GroupTheory.PResidual.Quotient
import all Theory.SpecificGroups.OmegaSixThree.TriangleLocal
/-!
# The local reversal centralizes the edge two-residual

The specified first-factor four-cycle rotates the negative edge two-space and
acts as minus the identity on its orthogonal four-space. The two literal
edge-vector characters take values in the two-element ternary unit group,
so the edge two-residual fixes both vectors. Orthogonality and the checked
reversal formula then prove the required centralization.

The single coordinate computation checks six basis vectors, without an edge
group catalogue or any enumeration of its elements.
Source: Aschbacher--Smith F.5.7(3), printed p.303.
-/

open Matrix SixTernaryCoordinates
namespace OmegaSixThree.TriangleLocal
open OrthogonalityGraph
public noncomputable section
private theorem reversal_word : edgeReversal =
    adjacentGenerator false 0 * adjacentGenerator false 2 * adjacentGenerator false 1 := by
  apply productEquiv.injective
  rw [edgeReversal_image,map_mul,map_mul]
  change (reversalPermutation,1)=
    toProduct (adjacentGenerator false 0)*toProduct (adjacentGenerator false 2)*
      toProduct (adjacentGenerator false 1)
  rw [adjacentGenerator_image,adjacentGenerator_image,adjacentGenerator_image]
  decide +kernel

private def reversalMatrix : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![1,1,0,0,0,1;1,1,0,0,0,-1;0,0,-1,0,0,0;0,0,0,-1,0,0;
     0,0,0,0,-1,0;1,-1,0,0,0,0]

-- t sends(e5,y,z) to(y,-e5,-z), and is -1 on the remaining three coordinates.
theorem edgeReversal_apply (v : Space) : edgeReversal.val.val v =
    ![v 0+v 1+v 5,v 0+v 1-v 5,-v 2,-v 3,-v 4,v 0-v 1] := by
  have he : edgeReversal.val.val.toLinearMap=Matrix.toLin' reversalMatrix := by
    rw [reversal_word]
    apply (Pi.basisFun (ZMod 3) (Fin 6)).ext
    intro j
    simp only [LinearEquiv.coe_coe,Pi.basisFun_apply,Matrix.toLin'_apply]
    revert j
    decide +kernel
  have he' := LinearMap.congr_fun he v
  change edgeReversal.val.val v = reversalMatrix *ᵥ v at he'
  rw [he']
  ext i
  fin_cases i <;> simp [reversalMatrix,Matrix.mulVec,Fin.sum_univ_succ,dotProduct,sub_eq_add_neg,add_assoc]

theorem edgeReversal_apply_pairing (v : Space) : edgeReversal.val.val v =
    -v + (-pairing v (e 5)+pairing v (e 0-e 1)) • e 5 +
      (-pairing v (e 5)-pairing v (e 0-e 1)) • (e 0-e 1) := by
  rw [edgeReversal_apply]
  ext i
  fin_cases i <;> simp [pairing,e] <;> ring_nf <;>
    simp [show (2:ZMod 3)=-1 by decide]

theorem edgeReversal_commutes_of_fix_vectors (g : omegaPlusSixThree)
    (hx : g.val (e 5)=e 5) (hy : g.val (e 0-e 1)=e 0-e 1) :
    edgeReversal.val*g=g*edgeReversal.val := by
  have hpair (v : Space) (w : Space) (hw : g.val w=w) :
      pairing (g.val v) w=pairing v w := by
    have h := pairing_orthogonal (Subgroup.inclusion omegaPlusSixThree_le_orthogonalGroup g) v w
    change pairing (g.val v) (g.val w)=pairing v w at h
    simpa only [hw] using h
  apply Subtype.ext
  ext v i
  change (edgeReversal.val.val (g.val v)) i=(g.val (edgeReversal.val.val v)) i
  rw [edgeReversal_apply_pairing,edgeReversal_apply_pairing,
    map_add,map_add,map_neg,map_smul,map_smul,hx,hy,hpair _ _ hx,hpair _ _ hy]

open Subgroup
local notation "E" => modelSystem.edgeGroup
private def edgeVector : Fin 2 → Space := ![e 5,e 0-e 1]
private def edgeCoordinate : Fin 2 → Fin 6 := ![5,0]
private theorem edgeVector_at (k : Fin 2) : edgeVector k (edgeCoordinate k)=1 := by
  revert k; decide +kernel

private theorem edge_signed (g : E) (k : Fin 2) : signed (g.val.val (edgeVector k)) (edgeVector k) := by
  fin_cases k
  · exact (point_eq_iff _ _ _ _).mp g.property.1
  · exact (point_eq_iff _ _ _ _).mp g.property.2

private def edgeScalar (k : Fin 2) (g : E) : ZMod 3 :=
  g.val.val (edgeVector k) (edgeCoordinate k)
private theorem edgeScalar_sq (k : Fin 2) (g : E) : edgeScalar k g*edgeScalar k g=1 := by
  rcases edge_signed g k with hh|hh <;>
    simp only [edgeScalar,hh,Pi.neg_apply,edgeVector_at] <;> ring
private theorem edge_eigen (k : Fin 2) (g : E) :
    g.val.val (edgeVector k)=edgeScalar k g • edgeVector k := by
  rcases edge_signed g k with hh|hh <;>
    simp only [edgeScalar,hh,Pi.neg_apply,edgeVector_at,one_smul,neg_smul]

private theorem edgeScalar_mul (k : Fin 2) (g h : E) :
    edgeScalar k (g*h)=edgeScalar k g*edgeScalar k h := by
  change (g.val.val (h.val.val (edgeVector k))) (edgeCoordinate k)=_
  rw [edge_eigen k h,map_smul]
  change edgeScalar k h*edgeScalar k g=_
  exact mul_comm _ _

/-- The literal action on each of the two negative edge vectors. -/
def edgeSign (k : Fin 2) : E →* (ZMod 3)ˣ where
  toFun g := ⟨edgeScalar k g,edgeScalar k g,edgeScalar_sq k g,edgeScalar_sq k g⟩
  map_one' := by
    apply Units.ext
    exact edgeVector_at k
  map_mul' g h := Units.ext (edgeScalar_mul k g h)

private theorem ternaryUnits_isTwoGroup : IsPGroup 2 (ZMod 3)ˣ := by
  apply IsPGroup.of_card (n:=1)
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem edgeResidual_fixes (g : E) (hg : g∈pResidual 2 E) (k : Fin 2) :
    g.val.val (edgeVector k)=edgeVector k := by
  have hh := pResidual_le_ker_of_isPGroup 2 (edgeSign k) ternaryUnits_isTwoGroup hg
  have he := congrArg (fun a : (ZMod 3)ˣ => a.val) (MonoidHom.mem_ker.mp hh)
  change edgeScalar k g=1 at he
  rw [edge_eigen k g,he,one_smul]

/-- The specified local reversal centralizes the actual edge two-residual. -/
theorem edgeReversal_commutes_twoResidual (g : E) (hg : g∈pResidual 2 E) :
    edgeReversal.val*g.val=g.val*edgeReversal.val :=
  edgeReversal_commutes_of_fix_vectors g.val (edgeResidual_fixes g hg 0) (edgeResidual_fixes g hg 1)

theorem edgeReversal_conj_twoResidual (g : E) (hg : g∈pResidual 2 E) :
    edgeReversal.val*g.val*edgeReversal.val⁻¹=g.val := by
  rw [edgeReversal_commutes_twoResidual g hg,mul_inv_cancel_right]

end
end OmegaSixThree.TriangleLocal
