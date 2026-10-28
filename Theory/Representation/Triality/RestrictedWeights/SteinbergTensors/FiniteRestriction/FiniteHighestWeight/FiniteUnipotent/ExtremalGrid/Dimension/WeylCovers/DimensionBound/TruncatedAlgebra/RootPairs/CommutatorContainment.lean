module
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.RootWeights
/-!
# Positive-root commutator containment from parameter relations

The exchange relation gives the sum-root commutator because that root commutes
with either summand. When no sum exists the root groups commute. Positive
root weights place the actual correction root in the required positive cone.
This discharges the input used to collect the literal finite-cell root order.
Source: GLS3 1.12.7(b), Steinberg 6.2(b).
-/

public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped commutatorElement
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
open RootPairGeometry
open ClassBound.ConnectedCentralizer.Bruhat.Coordinates.Normalization
universe u
variable {k:Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K:Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
private theorem sum_weight (S:Geometry K) {a b c:S.roots.Root} (hs:RootSum S a b c) :
    S.roots.rootWeight c = S.roots.rootWeight a * S.roots.rootWeight b := by
  have hp : S.roots.pairing b a = -1 := by
    apply Int.cast_injective (α:=ℝ)
    rw [S.based.1]
    norm_num only [Int.cast_neg,Int.cast_one]
    rw [d4_pairing_symm]
    exact d4_sum_pairing _ _ _ hs
  rw [← rootSum_reflection S hs,S.realized.2.2.2.2.2.1,hp]
  norm_num only [neg_neg,zpow_one]
  exact mul_comm _ _

omit [IsAlgClosed k] in
private theorem positive_nonopposite (S:Geometry K) {a b:S.roots.Root}
    (ha:a∈S.roots.positive) (hb:b∈S.roots.positive) : b≠S.roots.neg a := by
  intro h
  obtain ⟨_,_,_,_,_,_,_,_,hneg,_,hpos,_,_⟩ := S.realized
  rw [hpos] at ha hb
  change 0<S.roots.height a at ha
  change 0<S.roots.height b at hb
  rw [h,hneg] at hb
  omega

omit [IsAlgClosed k] in
private theorem commute_of_pairing_one (S:Geometry K) (hrel:RootPairParameterRelations S)
    (a b:S.roots.Root) (hp:(typeDRootPairing 2).pairing (S.rootIndex a) (S.rootIndex b)=1)
    (s t:k) : Commute ((rootCurve S a).onPoints (kPlusPoint s))
      ((rootCurve S b).onPoints (kPlusPoint t)) := by
  apply hrel.commute a b
  · intro h
    subst b
    rw [RootPairing.pairing_same] at hp
    norm_num at hp
  · intro h
    rw [h,S.based.2.2.1,RootPairing.pairing_reflectionPerm_self_right,
      RootPairing.pairing_same] at hp
    norm_num at hp
  · rintro ⟨c,hc⟩
    have hc' := d4_sum_pairing _ _ _ hc
    rw [hp] at hc'
    norm_num at hc'

/-- The actual parameter relations imply the subgroup commutator input. -/
theorem positiveCommutatorContainment_of_relations (S:Geometry K) (hrel:RootPairParameterRelations S) :
    PositiveCommutatorContainment S := by
  intro a ha b hb hab
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  obtain ⟨s,rfl⟩ := rootCurve_surjective S a x hx
  obtain ⟨t,rfl⟩ := rootCurve_surjective S b y hy
  by_cases hs:∃c,RootSum S a b c
  · obtain ⟨c,hc⟩ := hs
    obtain ⟨d,_,he⟩ := hrel.exchange a b c hc
    have hbc : (typeDRootPairing 2).pairing (S.rootIndex b) (S.rootIndex c)=1 := by
      rw [d4_pairing_symm]
      have hh := RootPairing.pairing_eq_add_of_root_eq_add
        (P:=typeDRootPairing 2) (l:=S.rootIndex b) hc
      rw [hh,RootPairing.pairing_same,d4_sum_pairing _ _ _ hc]
      norm_num
    have hcom := commute_of_pairing_one S hrel b c hbc t (d*s*t)
    have heq : ⁅(rootCurve S a).onPoints (kPlusPoint s),
        (rootCurve S b).onPoints (kPlusPoint t)⁆ =
      (rootCurve S c).onPoints (kPlusPoint (d*s*t)) := by
      rw [commutatorElement_def,he]
      rw [hcom.eq]
      group
    rw [heq]
    apply rootSubgroup_le_RootSubgroupGenerated S.roots
      (positiveCommutatorRoots_of_weight_eq S ha hb (show 0<1 by decide)
        (show 0<1 by decide) (by simpa only [pow_one] using sum_weight S hc))
    exact ((S.roots.rootSubgroup c).pointEquiv _).property
  · have hcomm := hrel.commute a b hab (positive_nonopposite S ha hb) hs s t
    have he : ⁅(rootCurve S a).onPoints (kPlusPoint s), (rootCurve S b).onPoints (kPlusPoint t)⁆=1 := by
      rw [commutatorElement_def,hcomm.eq]
      group
    rw [he]
    exact Subgroup.one_mem _
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
