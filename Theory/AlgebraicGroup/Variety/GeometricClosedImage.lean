module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import Theory.AlgebraicGroup.Variety.ProjectiveSpace

set_option linter.style.haveILetI false

/-!
# Constructible images of geometric varieties

This module proves the Chevalley image theorem for the scheme-backed geometric
varieties used in the algebraic-group development.  Every geometric morphism is
quasi-compact and locally of finite presentation: both source and target are of
finite type over a field, and the target is locally Noetherian.  Mathlib's
finite-presentation Chevalley theorem therefore makes its underlying
topological range constructible.

A dense constructible subset of a nonempty preirreducible space contains a
nonempty open subset.  Applying this to the canonical map into
`Morphism.schemeTheoreticRangeClosure` gives the open-range statement used in
orbit geometry.  Nonemptiness and preirreducibility of the closure are derived
from explicit source hypotheses and the canonical density of
`Scheme.Hom.toImage`; they are not hidden assumptions on the target.

Finally, over an algebraically closed field, rational points are the closed
scheme points.  The exported comparison shows that the rational-point range is
exactly the closed-point part of the scheme-theoretic range.  The reverse
inclusion uses that a nonempty locally closed fibre in a finite-type scheme over
an algebraically closed field contains a closed point.

The proof follows Chevalley's theorem (Stacks Project, Tags 054J and 054K) and
the standard Jacobson-space closed-point argument.  It is independent of group
structures, actions, and quotient constructions.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Topology

universe u

/-- A dense constructible subset of a nonempty preirreducible space contains a
nonempty open subset. -/
public theorem IsConstructible.exists_isOpen_nonempty_subset_of_dense
    {X : Type u} [TopologicalSpace X] [Nonempty X] [PreirreducibleSpace X]
    {S : Set X} (hS : IsConstructible S) (hSdense : Dense S) :
    ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ U ⊆ S := by
  induction hS using IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen _ =>
      exact ⟨U, hUopen, hSdense.nonempty, Set.Subset.rfl⟩
  | union S _ T _ hSih hTih =>
      by_cases hSc : closure S = Set.univ
      · obtain ⟨U, hUopen, hUne, hUS⟩ :=
          hSih (dense_iff_closure_eq.mpr hSc)
        exact ⟨U, hUopen, hUne, hUS.trans Set.subset_union_left⟩
      · have hTc : closure T = Set.univ := by
          by_contra hTc
          obtain ⟨x, hxS, hxT⟩ := nonempty_preirreducible_inter
            isClosed_closure.isOpen_compl isClosed_closure.isOpen_compl
            (Set.nonempty_compl.mpr hSc) (Set.nonempty_compl.mpr hTc)
          have hxrange : x ∈ closure (S ∪ T) := by
            rw [hSdense.closure_eq]
            trivial
          rw [closure_union] at hxrange
          exact hxrange.elim hxS hxT
        obtain ⟨U, hUopen, hUne, hUT⟩ :=
          hTih (dense_iff_closure_eq.mpr hTc)
        exact ⟨U, hUopen, hUne, hUT.trans Set.subset_union_right⟩
  | compl S _ hSih =>
      by_cases hSc : closure S = Set.univ
      · have hSdense' : Dense S := dense_iff_closure_eq.mpr hSc
        obtain ⟨U, hUopen, hUne, hUS⟩ := hSih hSdense'
        obtain ⟨x, hxU, hxSc⟩ :=
          hSdense.inter_open_nonempty U hUopen hUne
        exact False.elim (hxSc (hUS hxU))
      · exact ⟨(closure S)ᶜ, isClosed_closure.isOpen_compl,
          Set.nonempty_compl.mpr hSc,
          Set.compl_subset_compl.mpr subset_closure⟩

end Topology

namespace Theory.AlgebraicGroup.Variety.Geometric

open Topology

universe u

variable {k : Type u} [Field k]

private theorem morphism_locallyOfFiniteType {V W : Geometric k}
    (f : Morphism V W) : LocallyOfFiniteType f.hom := by
  haveI : LocallyOfFiniteType (f.hom ≫ W.structureMap) := by
    rw [f.commutes]
    infer_instance
  exact locallyOfFiniteType_of_comp f.hom W.structureMap

private theorem morphism_quasiCompact {V W : Geometric k}
    (f : Morphism V W) : QuasiCompact f.hom := by
  haveI : QuasiCompact (f.hom ≫ W.structureMap) := by
    rw [f.commutes]
    infer_instance
  exact QuasiCompact.of_comp f.hom W.structureMap

/-- The underlying scheme-point range of a geometric morphism is
constructible. -/
public theorem Morphism.range_isConstructible {V W : Geometric k}
    (f : Morphism V W) : IsConstructible (Set.range f.hom) := by
  letI : LocallyOfFiniteType f.hom := morphism_locallyOfFiniteType f
  letI : IsLocallyNoetherian W.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian W.structureMap
  letI : LocallyOfFinitePresentation f.hom := inferInstance
  letI : QuasiCompact f.hom := morphism_quasiCompact f
  letI : CompactSpace W.toScheme :=
    QuasiCompact.compactSpace_of_compactSpace W.structureMap
  letI : QuasiSeparatedSpace W.toScheme := inferInstance
  rw [← Set.image_univ]
  exact f.hom.isConstructible_image IsConstructible.univ

/-- A dense geometric morphism from an explicitly nonempty preirreducible
source has a range containing a nonempty open subset of the target. -/
public theorem Morphism.exists_isOpen_nonempty_subset_range_of_dense
    {V W : Geometric k} (f : Morphism V W)
    (hVnonempty : Nonempty V.toScheme)
    (hVirreducible : PreirreducibleSpace V.toScheme)
    (hf : DenseRange f.hom) :
    ∃ U : Set W.toScheme, IsOpen U ∧ U.Nonempty ∧ U ⊆ Set.range f.hom := by
  letI : Nonempty V.toScheme := hVnonempty
  letI : PreirreducibleSpace V.toScheme := hVirreducible
  letI : Nonempty W.toScheme := hf.nonempty_iff.mp inferInstance
  letI : PreirreducibleSpace W.toScheme := by
    refine ⟨?_⟩
    rw [← hf.closure_range]
    apply IsPreirreducible.closure
    rw [← Set.image_univ]
    exact PreirreducibleSpace.isPreirreducible_univ.image f.hom
      f.hom.continuous.continuousOn
  exact f.range_isConstructible.exists_isOpen_nonempty_subset_of_dense hf

/-- The canonical morphism to the reduced scheme-theoretic range closure has
dense underlying range. -/
public theorem Morphism.denseRange_toSchemeTheoreticRangeClosure
    {V W : Geometric k} (f : Morphism V W) :
    DenseRange f.toSchemeTheoreticRangeClosure.hom := by
  letI : QuasiCompact f.hom := morphism_quasiCompact f
  exact f.hom.toImage.denseRange

/-- The scheme-theoretic range closure of an explicitly nonempty
preirreducible source is irreducible. -/
public theorem Morphism.schemeTheoreticRangeClosure_isIrreducible
    {V W : Geometric k} (f : Morphism V W)
    (hVnonempty : Nonempty V.toScheme)
    (hVirreducible : PreirreducibleSpace V.toScheme) :
    IsIrreducible f.schemeTheoreticRangeClosure.toGeometric := by
  letI : Nonempty V.toScheme := hVnonempty
  letI : PreirreducibleSpace V.toScheme := hVirreducible
  let g := f.toSchemeTheoreticRangeClosure
  have hgDense : DenseRange g.hom :=
    f.denseRange_toSchemeTheoreticRangeClosure
  exact {
    toNonempty := hgDense.nonempty_iff.mp inferInstance
    isPreirreducible_univ := by
      rw [← hgDense.closure_range]
      apply IsPreirreducible.closure
      rw [← Set.image_univ]
      exact PreirreducibleSpace.isPreirreducible_univ.image g.hom
        g.hom.continuous.continuousOn }

/-- The image in the reduced scheme-theoretic range closure contains a
nonempty open subset.  The source hypotheses are explicit; density is supplied
by the canonical `toImage` factorization. -/
public theorem Morphism.exists_isOpen_nonempty_subset_rangeClosure
    {V W : Geometric k} (f : Morphism V W)
    (hVnonempty : Nonempty V.toScheme)
    (hVirreducible : PreirreducibleSpace V.toScheme) :
    ∃ U : Set f.schemeTheoreticRangeClosure.toGeometric.toScheme,
      IsOpen U ∧ U.Nonempty ∧
        U ⊆ Set.range f.toSchemeTheoreticRangeClosure.hom := by
  exact f.toSchemeTheoreticRangeClosure
    |>.exists_isOpen_nonempty_subset_range_of_dense
      hVnonempty hVirreducible f.denseRange_toSchemeTheoreticRangeClosure

/-- Evaluation at the closed point commutes with a geometric morphism. -/
@[simp]
public theorem Morphism.apply_closedPoint {V W : Geometric k}
    (f : Morphism V W) (x : Point V) :
    (f x).1 (IsLocalRing.closedPoint k) =
      f.hom (x.1 (IsLocalRing.closedPoint k)) := rfl

/-- Over an algebraically closed field, the closed-point part of the
scheme-point range is exactly the image of the rational-point range under
evaluation at the base closed point. -/
public theorem Morphism.image_pointRange_eq_range_inter_closedPoints
    [IsAlgClosed k] {V W : Geometric k} (f : Morphism V W) :
    (fun x : Point W => x.1 (IsLocalRing.closedPoint k)) '' Set.range f =
      Set.range f.hom ∩ closedPoints W.toScheme := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨⟨x.1 (IsLocalRing.closedPoint k), rfl⟩, ?_⟩
    exact (pointEquivClosedPoint W.structureMap (f x)).property
  · rintro ⟨⟨z, rfl⟩, hyclosed⟩
    letI : JacobsonSpace V.toScheme :=
      LocallyOfFiniteType.jacobsonSpace V.structureMap
    have hfiber_ne : (f.hom ⁻¹' {f.hom z}).Nonempty := ⟨z, rfl⟩
    have hfiber_lc : IsLocallyClosed (f.hom ⁻¹' {f.hom z}) :=
      (hyclosed.preimage f.hom.continuous).isLocallyClosed
    obtain ⟨z', hz'f, hz'closed⟩ :=
      nonempty_inter_closedPoints hfiber_ne hfiber_lc
    let x : Point V :=
      (pointEquivClosedPoint V.structureMap).symm ⟨z', hz'closed⟩
    refine ⟨f x, ⟨x, rfl⟩, ?_⟩
    change f.hom (x.1 (IsLocalRing.closedPoint k)) = f.hom z
    rw [show x.1 (IsLocalRing.closedPoint k) = z' by
      exact congrArg Subtype.val
        ((pointEquivClosedPoint V.structureMap).apply_symm_apply
          ⟨z', hz'closed⟩)]
    exact hz'f

/-- A rational point lies in the point range exactly when its associated
closed scheme point lies in the underlying scheme-point range. -/
public theorem Morphism.point_mem_range_iff_closedPoint_mem_range
    [IsAlgClosed k] {V W : Geometric k} (f : Morphism V W) (y : Point W) :
    y ∈ Set.range f ↔
      y.1 (IsLocalRing.closedPoint k) ∈ Set.range f.hom := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1 (IsLocalRing.closedPoint k), rfl⟩
  · intro hy
    have hyclosed :
        y.1 (IsLocalRing.closedPoint k) ∈ closedPoints W.toScheme :=
      (pointEquivClosedPoint W.structureMap y).property
    have hyimage : y.1 (IsLocalRing.closedPoint k) ∈
        (fun x : Point W => x.1 (IsLocalRing.closedPoint k)) '' Set.range f := by
      rw [f.image_pointRange_eq_range_inter_closedPoints]
      exact ⟨hy, hyclosed⟩
    obtain ⟨y', hy'range, hy'eq⟩ := hyimage
    have hyy' : y' = y := by
      apply (pointEquivClosedPoint W.structureMap).injective
      exact Subtype.ext hy'eq
    rwa [hyy'] at hy'range

/-- A nonempty open subset of a geometric variety over an algebraically
closed field contains the closed point associated to a rational point. -/
public theorem exists_point_closedPoint_mem_of_isOpen
    [IsAlgClosed k] (V : Geometric k) {U : Set V.toScheme}
    (hUopen : IsOpen U) (hUne : U.Nonempty) :
    ∃ x : Point V, x.1 (IsLocalRing.closedPoint k) ∈ U := by
  letI : JacobsonSpace V.toScheme :=
    LocallyOfFiniteType.jacobsonSpace V.structureMap
  obtain ⟨z, hzU, hzclosed⟩ :=
    nonempty_inter_closedPoints hUne hUopen.isLocallyClosed
  let x : Point V :=
    (pointEquivClosedPoint V.structureMap).symm ⟨z, hzclosed⟩
  refine ⟨x, ?_⟩
  rw [show x.1 (IsLocalRing.closedPoint k) = z by
    exact congrArg Subtype.val
      ((pointEquivClosedPoint V.structureMap).apply_symm_apply
        ⟨z, hzclosed⟩)]
  exact hzU

/-- The range-closure factorization agrees with the original morphism on
rational points after applying the closed immersion. -/
@[simp]
public theorem Morphism.toSchemeTheoreticRangeClosure_inclusion_apply
    {V W : Geometric k} (f : Morphism V W) (x : Point V) :
    f.schemeTheoreticRangeClosure.inclusion
        (f.toSchemeTheoreticRangeClosure x) = f x := by
  apply Subtype.ext
  change (x.1 ≫ f.hom.toImage) ≫ f.hom.imageι = x.1 ≫ f.hom
  rw [Category.assoc, Scheme.Hom.toImage_imageι]

/-- Point membership in the range-closure factorization is equivalent to
membership of the included point in the original rational-point range. -/
public theorem Morphism.point_mem_rangeClosure_iff_inclusion_mem_range
    {V W : Geometric k} (f : Morphism V W)
    (y : Point f.schemeTheoreticRangeClosure.toGeometric) :
    y ∈ Set.range f.toSchemeTheoreticRangeClosure ↔
      f.schemeTheoreticRangeClosure.inclusion y ∈ Set.range f := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, f.toSchemeTheoreticRangeClosure_inclusion_apply x |>.symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply (cancel_mono f.schemeTheoreticRangeClosure.inclusion.hom).mp
    change (f.toSchemeTheoreticRangeClosure x).1 ≫
        f.schemeTheoreticRangeClosure.inclusion.hom =
      y.1 ≫ f.schemeTheoreticRangeClosure.inclusion.hom
    have hx' := congrArg (fun z : Point W => z.1) hx
    rw [show (f.toSchemeTheoreticRangeClosure x).1 ≫
        f.schemeTheoreticRangeClosure.inclusion.hom = (f x).1 by
      exact congrArg (fun z : Point W => z.1)
        (f.toSchemeTheoreticRangeClosure_inclusion_apply x)]
    exact hx'

end Theory.AlgebraicGroup.Variety.Geometric
