module
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.RootCoordinates.Source
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedRootTorus.RootStability
/-!
# Graph-field action on the two actual ordered root charts

The three diagram-orbit blocks consist of commuting root groups, as follows
from the actual parameter relations and their orthogonal root coordinates.
Reordering only these blocks identifies graph-field action with the literal
inverse-reindexed coefficient Frobenius. The opposite chart retains the same
permutation and scalar convention.
Source: Steinberg 6.2(b), 11.8 and 13.3(a).
-/

public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
open CyclicDimension CyclicDimension.RootPairGeometry ClassBound ClassBound.FixedRootTorus
open Standard.PositiveCoordinates
universe u
variable {k:Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K:Variety k} [AlgebraicGroup K]

private def positiveCoords : Fin 12 → Fin 4 → ℤ :=
  ![![1,-1,0,0], ![0,0,1,-1], ![0,0,1,1], ![0,1,-1,0],
    ![1,0,-1,0], ![0,1,0,-1], ![0,1,0,1], ![1,0,0,-1],
    ![0,1,1,0], ![1,0,0,1], ![1,0,1,0], ![1,1,0,0]]

private theorem positiveCoords_spec (i : Fin 12) (j : Fin 4) :
    ((typeDRootPairing 2).root (rootIndex i) : Vec 4) j = (positiveCoords i j : ℝ) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [positiveCoords, rootIndex, difference, sumRoot, typeDRootPairing_root_val,
      typeDRootEmbedding, typeDRootVector, basisVector, Pi.single_apply, Fin.ext_iff]

private theorem diagram_pairing (i:Fin 12) (hi:i≠diagram i) :
    (typeDRootPairing 2).pairing (rootIndex i) (rootIndex (diagram i))=0 := by
  have hint : ∀ i:Fin 12, i≠diagram i →
      (∑ j:Fin 4, positiveCoords (diagram i) j * positiveCoords i j)=0 := by
    decide +kernel
  have h:=hint i hi
  rw [typeDRootPairing_pairing]
  change (∑ j:Fin 4, ((typeDRootPairing 2).root (rootIndex (diagram i)):Vec 4) j *
    ((typeDRootPairing 2).root (rootIndex i):Vec 4) j)=0
  simp only [positiveCoords_spec]
  exact_mod_cast h

omit [IsAlgClosed k] in
private theorem rootPoint_diagram_commute (S:Geometry K) (hrel:RootPairParameterRelations S)
    (i:Fin 12) (s t:k) : Commute
      ((rootCurve S (positiveCoordinateRoot S i)).onPoints (kPlusPoint s))
      ((rootCurve S (positiveCoordinateRoot S (diagram i))).onPoints (kPlusPoint t)) := by
  by_cases hi:i=diagram i
  · rw [← hi]
    have hc : Commute (kPlusPoint s) (kPlusPoint t) := by
      apply (additiveGroupPointEquiv k).injective
      change Multiplicative.ofAdd (s+t)=Multiplicative.ofAdd (t+s)
      exact congrArg Multiplicative.ofAdd (add_comm s t)
    exact hc.map (rootCurve S (positiveCoordinateRoot S i)).onPoints
  · have hp:(typeDRootPairing 2).pairing (S.rootIndex (positiveCoordinateRoot S i))
        (S.rootIndex (positiveCoordinateRoot S (diagram i)))=0 := by
      simpa only [positiveCoordinateRoot,Equiv.apply_symm_apply] using diagram_pairing i hi
    apply hrel.commute
    · intro h
      have he := congrArg S.rootIndex h
      exact hi (rootIndex_injective (by simpa only [positiveCoordinateRoot,
        Equiv.apply_symm_apply] using he))
    · intro h
      rw [h,S.based.2.2.1,RootPairing.pairing_reflectionPerm_self_right,
        RootPairing.pairing_same] at hp
      norm_num at hp
    · rintro ⟨c,hc⟩
      have hc' := d4_sum_pairing _ _ _ hc
      rw [hp] at hc'
      norm_num at hc'

private theorem prod_blocks {G:Type*} [Monoid G] (f:Fin 12→G) :
    (List.ofFn f).prod=(f 0*f 1*f 2)*f 3*(f 4*f 5*f 6)*
      (f 7*f 8*f 9)*f 10*f 11 := by
  simp [List.ofFn_succ,mul_assoc]

private theorem prod_diagram {G:Type*} [Monoid G] (f:Fin 12→G)
    (h:∀i,Commute (f i) (f (diagram i))) :
    (List.ofFn fun i=>f (diagram i)).prod=(List.ofFn f).prod := by
  have rot (i:Fin 12) : f (diagram i)*f (diagram (diagram i))*f i=
      f i*f (diagram i)*f (diagram (diagram i)) := by
    have h2:=h (diagram (diagram i))
    rw [diagram_three] at h2
    exact ((h i).mul_right h2.symm).eq.symm.trans (mul_assoc _ _ _).symm
  have h0:=rot 0
  have h4:=rot 4
  have h7:=rot 7
  rw [prod_blocks,prod_blocks]
  change f 1*f 2*f 0=f 0*f 1*f 2 at h0
  change f 5*f 6*f 4=f 4*f 5*f 6 at h4
  change f 8*f 9*f 7=f 7*f 8*f 9 at h7
  change (f 1*f 2*f 0)*f 3*(f 5*f 6*f 4)*(f 8*f 9*f 7)*f 10*f 11=_
  rw [h0,h4,h7]

omit [IsAlgClosed k] in
private theorem diagram_coordinateRoot (S:Geometry K) (i:Fin 12) :
    diagramRoot S (positiveCoordinateRoot S i)=positiveCoordinateRoot S (diagram i) := by
  simp only [diagramRoot,positiveCoordinateRoot,Equiv.trans_apply,Equiv.apply_symm_apply,
    diagram_rootIndex]

omit [IsAlgClosed k] in
/-- Graph-field equivariance of the literal ordered positive root product. -/
theorem positive_ordered_graphField (S:Geometry K) (hrel:RootPairParameterRelations S) (n:ℕ) (x:Fin 12→k) :
    graphFieldEnd S n (orderedRootPoint S (positiveCoordinateRoot S) x)=
      orderedRootPoint S (positiveCoordinateRoot S)
        (fun i=>x (diagram.symm i)^(2^n)) := by
  change graphFieldEnd S n
    ((List.ofFn fun i=>rootElement S (positiveCoordinateRoot S i) (x i)).prod)=_
  rw [map_list_prod,List.map_ofFn]
  simp only [Function.comp_def,graphFieldEnd_rootElement,diagram_coordinateRoot]
  have h:=prod_diagram
    (fun i=>rootElement S (positiveCoordinateRoot S i) (x (diagram.symm i)^(2^n)))
    (fun i=>rootPoint_diagram_commute S hrel i _ _)
  simpa only [Equiv.symm_apply_apply,orderedRootPoint,rootElement] using h

/-- The opposite ordered product has the same coefficient twist. -/
theorem negative_ordered_graphField (S:Geometry K) (hrel:RootPairParameterRelations S)
    (n:ℕ) (x:Fin 12→k) :
    graphFieldEnd S n (orderedRootPoint S (negativeCoordinateRoot S) x)=
      orderedRootPoint S (negativeCoordinateRoot S)
        (fun i=>x (diagram.symm i)^(2^n)) :=
  positive_ordered_graphField S.opposite (rootPairParameterRelations_opposite S hrel) n x
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
