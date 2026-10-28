module

public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.Affine
public import Theory.AlgebraicGroup.Variety.OpenSubvariety

/-!
# Scheme factorization through a projective chart

For geometric varieties over an algebraically closed field, rational-point
containment in an open subset implies containment of the entire scheme image:
a nonempty closed complement would contain a closed rational point. We apply
the actual open-immersion universal property to obtain a chart morphism, with
exact factorization and evaluation equations. Closed-point extensionality and
point lifting provide the corresponding uniqueness statements.

These bridges are used both for projective-line rigidity (Borel 10.8) and for
regular projective-linear coordinate constructions in algebraic families.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
noncomputable section
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Equality on rational points determines geometric morphisms over an algebraically closed field. -/
theorem morphism_eq_of_pointwise_eq {V W : Geometric k} (f g : Morphism V W)
    (h : ∀ x : Point V, f x = g x) : f = g := by
  let : LocallyOfFiniteType (f.hom ≫ W.structureMap) := by
    rw [f.commutes]
    infer_instance
  apply Morphism.ext
  apply AlgebraicGeometry.ext_of_apply_eq W.structureMap
      (Set.univ : Set V.toScheme) isOpen_univ.isLocallyClosed dense_univ
  · intro x _ hx
    let p : Point V := ⟨pointOfClosedPoint V.structureMap x hx,
      pointOfClosedPoint_comp V.structureMap x hx⟩
    have hp : p.val (IsLocalRing.closedPoint k) = x :=
      pointOfClosedPoint_apply V.structureMap x hx _
    calc
      f.hom x = f.hom (p.val (IsLocalRing.closedPoint k)) := congrArg f.hom hp.symm
      _ = g.hom (p.val (IsLocalRing.closedPoint k)) := by
        change (f p).val (IsLocalRing.closedPoint k) = (g p).val (IsLocalRing.closedPoint k)
        rw [h p]
      _ = g.hom x := congrArg g.hom hp
  · exact f.commutes.trans g.commutes.symm

theorem morphism_range_subset_open_of_points {V W : Geometric k}
    (f : Morphism V W) (U : W.toScheme.Opens)
    (hf : ∀ p : Point V, (f p).val (IsLocalRing.closedPoint k) ∈ U) :
    Set.range f.hom ⊆ U := by
  let : JacobsonSpace V.toScheme := LocallyOfFiniteType.jacobsonSpace V.structureMap
  rintro _ ⟨x,rfl⟩
  by_contra hx
  have hc : IsClosed (f.hom ⁻¹' (U : Set W.toScheme)ᶜ) :=
    U.isOpen.isClosed_compl.preimage f.hom.continuous
  obtain ⟨y,hy,hclosed⟩ := nonempty_inter_closedPoints ⟨x,hx⟩ hc.isLocallyClosed
  let p : Point V := ⟨pointOfClosedPoint V.structureMap y hclosed,
    pointOfClosedPoint_comp V.structureMap y hclosed⟩
  have hp : p.val (IsLocalRing.closedPoint k) = y :=
    pointOfClosedPoint_apply V.structureMap y hclosed _
  apply hy
  have hh := hf p
  change f.hom (p.val (IsLocalRing.closedPoint k)) ∈ U at hh
  rwa [hp] at hh

/-- Genuine factorization through a projective affine chart, detected on rational points. -/
def chartLift {V : Geometric k} (i : Fin 2) (f : Morphism V (projectiveLine k))
    (hf : ∀ p : Point V, (f p).val (IsLocalRing.closedPoint k) ∈ projectiveLineChartOpen k i) :
    Morphism V (polynomialAffineLine k) where
  hom := IsOpenImmersion.lift (projectiveLineChartInclusion (k := k) i).hom f.hom (by
    rw [← Scheme.Hom.coe_opensRange (projectiveLineChartInclusion (k := k) i).hom,projectiveLineChartInclusion_opensRange]
    exact morphism_range_subset_open_of_points f _ hf)
  commutes := by
    rw [← (projectiveLineChartInclusion (k := k) i).commutes,← Category.assoc,
      IsOpenImmersion.lift_fac,f.commutes]

@[simp] theorem chartLift_inclusion {V : Geometric k} (i : Fin 2)
    (f : Morphism V (projectiveLine k)) (hf) :
    Morphism.comp (chartLift i f hf) (projectiveLineChartInclusion i) = f := by
  apply Morphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

@[simp] theorem chartLift_apply {V : Geometric k} (i : Fin 2)
    (f : Morphism V (projectiveLine k)) (hf) (p : Point V) :
    projectiveLineChartInclusion i (chartLift i f hf p) = f p := by
  simpa only [Morphism.comp_apply_point] using
    congrArg (fun m : Morphism V (projectiveLine k) => m p) (chartLift_inclusion i f hf)

omit [IsAlgClosed k] in
theorem chartInclusion_injective (i : Fin 2) :
    Function.Injective (projectiveLineChartInclusion (k := k) i) := by
  intro x y he
  apply Subtype.ext
  apply (cancel_mono (projectiveLineChartInclusion (k := k) i).hom).mp
  exact congrArg Subtype.val he

omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency false in
theorem point_mem_chart_iff (i : Fin 2) (x : Point (projectiveLine k)) :
    x.val (IsLocalRing.closedPoint k) ∈ projectiveLineChartOpen k i ↔
      ∃ y : Point (polynomialAffineLine k), projectiveLineChartInclusion i y = x := by
  constructor
  · intro hx
    have hrange : Set.range x.val ⊆ Set.range (projectiveLineChartInclusion (k := k) i).hom := by
      rw [← Scheme.Hom.coe_opensRange (projectiveLineChartInclusion (k := k) i).hom,projectiveLineChartInclusion_opensRange]
      rintro _ ⟨z,rfl⟩
      have hz : z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      subst z
      exact hx
    let y : Point (polynomialAffineLine k) :=
      ⟨IsOpenImmersion.lift (projectiveLineChartInclusion (k := k) i).hom x.val hrange, by
        rw [← (projectiveLineChartInclusion (k := k) i).commutes,← Category.assoc,
          IsOpenImmersion.lift_fac,x.property]⟩
    refine ⟨y,?_⟩
    apply Subtype.ext
    exact IsOpenImmersion.lift_fac _ _ _
  · rintro ⟨y,rfl⟩
    change (projectiveLineChartInclusion (k := k) i).hom
      (y.val (IsLocalRing.closedPoint k)) ∈ _
    rw [← projectiveLineChartInclusion_opensRange]
    change (projectiveLineChartInclusion (k := k) i).hom
      (y.val (IsLocalRing.closedPoint k)) ∈ Set.range (projectiveLineChartInclusion (k := k) i).hom
    exact ⟨_,rfl⟩

end
end Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
