module

public import Theory.Representation.Triality.RestrictedWeights.ConcreteGeometry
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound
/-!
# Actual simple-root generation for the finite triality geometry

The literal root curves are the anchored Clifford root points. The already
proved generation by the eight signed simple roots therefore gives generation
of the whole point monoid; in characteristic two each generator is its own
inverse. This discharges the point-generation premise in the cyclic coefficient
algebra argument. The final consumer retains only operator normalization and
containment of the simple-root orbits of the cyclic vector.
Source: GLS3 §§1.9–1.12; Steinberg §§6 and 13.2(d).
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.RestrictedWeights.SteinbergTensors FiniteRestriction
open ExtremalGrid.CyclicDimension
namespace Triality.RestrictedWeights.Concrete
@[expose] public noncomputable section
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu : IsUniversalVersion (groupVariety k))

theorem rootCurve_point (r : (finiteGeometry k hu).roots.Root) (a : k) :
    (rootCurve (finiteGeometry k hu) r).onPoints (kPlusPoint a) = rootPoint k r.down a :=
  pinnedRootParametrization_inclusion k r a

theorem rootCurve_negative (i : Fin 4) (a : k) :
    (rootCurve (finiteGeometry k hu)
      ((finiteGeometry k hu).roots.neg ((finiteGeometry k hu).simpleRoot i).val)).onPoints
      (kPlusPoint a) = negativeSimplePoint k i a := by
  rw [rootCurve_point]
  change rootPoint k ((pinnedRootData k).neg (pinnedRootIndex k (simpleRoot i))).down a = _
  rw [pinnedRootData_neg]
  rfl

theorem simpleRootPoints_eq : simpleRootPoints (finiteGeometry k hu) =
    Set.range (fun p : Fin 4 × k => positiveSimplePoint k p.1 p.2) ∪
    Set.range (fun p : Fin 4 × k => negativeSimplePoint k p.1 p.2) := by
  ext x
  constructor
  · rintro ⟨⟨i,b,a⟩,rfl⟩
    cases b
    · exact Or.inr ⟨⟨i,a⟩,(rootCurve_negative k hu i a).symm⟩
    · exact Or.inl ⟨⟨i,a⟩,(rootCurve_point k hu _ a).symm⟩
  · rintro (⟨⟨i,a⟩,rfl⟩ | ⟨⟨i,a⟩,rfl⟩)
    · exact ⟨⟨i,true,a⟩,rootCurve_point k hu _ a⟩
    · exact ⟨⟨i,false,a⟩,rootCurve_negative k hu i a⟩

theorem simpleRootPoints_generate :
    Submonoid.closure (simpleRootPoints (finiteGeometry k hu)) = ⊤ := by
  have hgen : Subgroup.closure (simpleRootPoints (finiteGeometry k hu)) = ⊤ := by
    rw [simpleRootPoints_eq]
    exact simplePointSubgroup_eq_top k
  have hinv : (simpleRootPoints (finiteGeometry k hu))⁻¹ =
      simpleRootPoints (finiteGeometry k hu) := by
    have hself (x) (hx : x ∈ simpleRootPoints (finiteGeometry k hu)) : x⁻¹ = x := by
      obtain ⟨⟨i,b,a⟩,rfl⟩ := hx
      dsimp only
      rw [rootCurve_point,rootPoint_inv]
    ext x
    change x⁻¹ ∈ simpleRootPoints (finiteGeometry k hu) ↔
      x ∈ simpleRootPoints (finiteGeometry k hu)
    constructor
    · intro hx
      have he := hself x⁻¹ hx
      rw [inv_inv] at he
      exact he.symm ▸ hx
    · intro hx
      simpa only [hself x hx] using hx
  have he := congrArg Subgroup.toSubmonoid hgen
  rw [Subgroup.closure_toSubmonoid,hinv,Set.union_self] at he
  exact he
theorem operatorOrbit_eq_top_of_simple_orbits
    {V : Type*} [AddCommGroup V] [Module k V]
    (rho : RationalRepresentation (groupVariety k) V)
    (A : Subalgebra k (Module.End k V)) (hnorm : Normalizes rho A)
    (v : V) (hcyc : IsCyclicRepresentation rho v)
    (hroot : ∀ g ∈ simpleRootPoints (finiteGeometry k hu),
      (rho.action g).val v ∈ operatorOrbit A v) : operatorOrbit A v = ⊤ :=
  operatorOrbit_eq_top rho A hnorm v hcyc _ (simpleRootPoints_generate k hu) hroot
end
end Triality.RestrictedWeights.Concrete
