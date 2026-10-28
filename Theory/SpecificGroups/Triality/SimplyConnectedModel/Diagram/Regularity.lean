module

public import Theory.AlgebraicGroup.Morphism.GeneratedRegularity
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Diagram.Regularity.RootCurves
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Diagram.Regularity.SpinTangents

/-!
# Coordinate descent for a pinned Spin point map

Regularity on the genuine coroot torus and on all closed root subgroups gives
regular connected generators for the graph of a pinned point homomorphism.
The embedded torus and root tangents span the concrete Clifford Spin tangent
by the dimension calculation in `Regularity.SpinTangents`. The general
closed-graph descent theorem therefore constructs a global morphism, and its
polynomial-function pullback has the exact evaluation formula.

Only the pinned point homomorphism is an input. No regularity or tangent-span
premise remains, and no regular inverse to the Spin-to-Omega point bijection is
used. Existence of the pinned point homomorphism is a separate construction.

Source: GLS3, Theorem 1.15.2(a), and Steinberg (6.2)(b–c),
`refs/KGroup/GLS3/Chapter1.tex` and `Chapter2St2.tex`.
-/

public section
noncomputable section
namespace Triality.SimplyConnected.Diagram
open Theory Theory.AlgebraicGroup
open Pinning
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

private def generatorSubgroup : Option RootIndex → ClosedSubgroup (groupVariety k)
  | none => CorootTorus.closedSubgroup k
  | some r => rootClosedSubgroup k r

/-- Actual tangent spanning suffices for global regularity of the pinned point
map. All graph-closedness and polynomial-coordinate descent inputs are proved. -/
theorem IsPinned.exists_morphism_of_torus_root_tangent_span
    {f : Points k →* Points k} (hf : IsPinned k f)
    (hspan : LinearMap.range
        (Bor1.identityTangentMorphismLinearMap (CorootTorus.closedSubgroup k).inclusion) ⊔
      (⨆ r : RootIndex, LinearMap.range
        (Bor1.identityTangentMorphismLinearMap (rootClosedSubgroup k r).inclusion)) = ⊤) :
    ∃ F : AlgebraicGroup.Morphism (groupVariety k) (groupVariety k), F.onPoints = f := by
  let A (i : Option RootIndex) := (generatorSubgroup k i).carrierVariety
  let : ∀ i, AlgebraicGroup (A i) := fun i => (generatorSubgroup k i).carrierAlgebraicGroup
  let a (i : Option RootIndex) : AlgebraicGroup.Morphism (A i) (groupVariety k) :=
    (generatorSubgroup k i).inclusion
  have hb : ∀ i, ∃ b : AlgebraicGroup.Morphism (A i) (groupVariety k),
      ∀ x, f ((a i).onPoints x) = b.onPoints x := by
    intro i
    cases i with
    | none =>
        exact ⟨(CorootTorus.closedSubgroup k).inclusion.comp (torusMap k),
          hf.torus_inclusion k⟩
    | some r =>
        obtain ⟨b, hb⟩ := hf.exists_rootRestriction k r
        exact ⟨b, fun x => (hb x).symm⟩
  choose b hb using hb
  refine AlgebraicGroup.Morphism.exists_of_connected_generators_of_tangent_span
    f A a b ?_ ?_ hb ?_
  · intro i
    cases i with
    | none => exact (CorootTorus.isSubtorus k).isConnected
    | some r => exact (rootClosedSubgroup_isOneParameter k r).isConnected
  · apply top_unique
    rw [← allRootPointSubgroup_eq_top k]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨⟨r, t⟩, rfl⟩
    apply Subgroup.subset_closure
    exact Set.mem_iUnion.mpr ⟨some r, rootSubgroupPoint k r t,
      rootSubgroupPoint_inclusion k r t⟩
  · rw [iSup_option]
    exact hspan

/-- The descended coordinate-ring map evaluates by precomposition with the
prescribed point map on the actual closed Clifford Spin variety. -/
theorem IsPinned.exists_pullback_of_torus_root_tangent_span
    {f : Points k →* Points k} (hf : IsPinned k f)
    (hspan : LinearMap.range
        (Bor1.identityTangentMorphismLinearMap (CorootTorus.closedSubgroup k).inclusion) ⊔
      (⨆ r : RootIndex, LinearMap.range
        (Bor1.identityTangentMorphismLinearMap (rootClosedSubgroup k r).inclusion)) = ⊤) :
    ∃ pull : Variety.PolynomialFunction (groupVariety k) →ₐ[k]
        Variety.PolynomialFunction (groupVariety k),
      ∀ a x, pull a x = a (f x) := by
  obtain ⟨F, hF⟩ := hf.exists_morphism_of_torus_root_tangent_span k hspan
  refine ⟨F.toVariety.pullbackAlgHom, ?_⟩
  intro a x
  change a (F.onPoints x) = a (f x)
  rw [hF]

/-- Every pinned point homomorphism of the actual Clifford Spin D4 group is
regular. The concrete torus and root tangent calculation discharges the
separability premise of closed-graph coordinate descent. -/
theorem IsPinned.exists_morphism
    {f : Points k →* Points k} (hf : IsPinned k f) :
    ∃ F : AlgebraicGroup.Morphism (groupVariety k) (groupVariety k), F.onPoints = f :=
  hf.exists_morphism_of_torus_root_tangent_span k (torus_root_tangent_span k)

/-- Polynomial functions pull back along the pinned point homomorphism on the
actual closed Clifford Spin variety, with their prescribed values everywhere. -/
theorem IsPinned.exists_pullback
    {f : Points k →* Points k} (hf : IsPinned k f) :
    ∃ pull : Variety.PolynomialFunction (groupVariety k) →ₐ[k]
        Variety.PolynomialFunction (groupVariety k),
      ∀ a x, pull a x = a (f x) :=
  hf.exists_pullback_of_torus_root_tangent_span k (torus_root_tangent_span k)

end Triality.SimplyConnected.Diagram
