module
public import Theory.Representation.Triality.RestrictedWeights.ConcreteTorusGeometry.Normalizer
public import Theory.Representation.Triality.RestrictedWeights.ConcreteRankOne
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusGeometry
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusGeometry.SemisimpleContainment
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusGeometry.PinnedMaps
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TwistedKernels
public import Theory.AlgebraicGroup.Solvable.SemisimpleConjugacy
public import Theory.AlgebraicGroup.Jordan.ClosedSubgroup
/-!
# The source ambient triality odd-class bound

Borel element coverage and semisimple conjugacy inside its genuine torus/radical
factorization place every semisimple element in the chosen torus. The actual
normalizer construction supplies Weyl fusion. Pinned Frobenius/diagram maps and
the proved integral D4 twisted-kernel calculation then bound the ambient image
of odd-order fixed classes by q^4. Fixed-group fusion is a separate consumer.
Source: Steinberg 12.5, 14.7–14.9; GLS3 2.8.2.
-/
public noncomputable section
open Theory.AlgebraicGroup
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.RestrictedWeights.SteinbergTensors FiniteRestriction ClassBound
namespace Triality.RestrictedWeights.Concrete.TorusGeometrySource
universe u
variable (k:Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu:IsUniversalVersion (groupVariety k))

theorem semisimple_conjugate_geometry {K:Variety k} [AlgebraicGroup K] (S:Geometry K) (x:K.Point)
    (hx:IsSemisimpleElement K x) :
    ∃ t:S.torus.carrierVariety.Point,
      IsConj x (S.torus.includePoint t) := by
  let B := S.bigCell.data.B
  let := B.carrierAlgebraicGroup
  let T := B.inclusion.closedSubgroupPreimage S.torus
  let U := B.inclusion.closedSubgroupPreimage S.bigCell.data.positive_witness.unipotent
  let := U.carrierAlgebraicGroup
  obtain ⟨g,hg⟩ := BorelElementCoverage.exists_conjugate_mem S.simple.1 S.bigCell.data.B_isBorel x
  let c : Theory.AlgebraicGroup.Morphism K K :=
    { toVariety := Theory.AlgebraicGroup.conjugationByMorphism _ g⁻¹
      map_one := by simp [Theory.AlgebraicGroup.conjugationByMorphism_apply]
      map_mul := by intro a b; simp only [Theory.AlgebraicGroup.conjugationByMorphism_apply];group }
  have hc : IsSemisimpleElement K (g⁻¹*x*g) := by
    have hc := morphism_preserves_semisimpleElement c x hx
    change IsSemisimpleElement K (g⁻¹*x*(g⁻¹)⁻¹) at hc
    simpa only [inv_inv] using hc
  let y := B.pointEquiv.symm ⟨g⁻¹*x*g,hg⟩
  have hy : B.inclusion.onPoints y=g⁻¹*x*g := congrArg Subtype.val (B.pointEquiv.apply_symm_apply _)
  have hs : IsSemisimpleElement B.carrierVariety y :=
    (closedSubgroup_semisimpleElement_iff B hg).mp hc
  obtain ⟨hT,hUc,hU,hUn,hfac⟩ := AmbientCount.TorusGeometry.chosen_borel_internal_factors S
  obtain ⟨a,_,ha⟩ := semisimpleElement_conjugate_into_subtorus_of_unipotent_factorization
    T U hT hUc hU hUn hfac y hs
  have hmem : (B.inclusion.onPoints a)⁻¹*(g⁻¹*x*g)*B.inclusion.onPoints a∈S.torus.toSubgroup := by
    change B.inclusion.onPoints (a⁻¹*y*a)∈S.torus.toSubgroup at ha
    simpa only [map_mul,map_inv,hy] using ha
  let t := S.torus.pointEquiv.symm ⟨_,hmem⟩
  refine ⟨t,isConj_iff.mpr ⟨(g*B.inclusion.onPoints a)⁻¹,?_⟩⟩
  have ht := congrArg Subtype.val (S.torus.pointEquiv.apply_symm_apply ⟨_,hmem⟩)
  change S.torus.includePoint t=_ at ht
  rw [ht]
  group

def torusData (n:ℕ) : AmbientCount.TorusData (finiteGeometry k hu) n :=
  AmbientCount.TorusGeometry.torusData (weylGeometry k hu)
    (Classical.choice (AmbientCount.TorusGeometry.nonempty_pinnedTorusMaps (finiteGeometry k hu)))
    (semisimple_conjugate_geometry k (finiteGeometry k hu)) n

theorem ambientClassBound (n:ℕ) (hn:0<n) : AmbientClassBound (finiteGeometry k hu) n :=
  ambientClassBound_of_torusData _ n hn (torusData k hu n)
    (AmbientCount.twistedKernel_finite (torusData k hu n) hn)
    (AmbientCount.kernelTotal_eq (torusData k hu n) hn)
end Triality.RestrictedWeights.Concrete.TorusGeometrySource
