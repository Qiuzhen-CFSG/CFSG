module

public import Theory.AlgebraicGroup.Bor1.MorphicActionOrbitGeometry
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit.StabilizerFiber
-- This continuation of orbit geometry proves the public boundary equations below.
-- The source keeps the boundary definitions' bodies private, so only this proof
-- module imports those implementations; downstream proofs can use the equations.
import all Theory.AlgebraicGroup.Bor1.MorphicActionOrbitGeometry

/-!
# Minimal-dimensional orbits are closed

The orbit carrier and its closure have the same Krull dimension, also for a
disconnected acting group. To compare dimensions across components, each finite
chain of irreducible closed subsets is placed in an irreducible component, and
a dense open meets every component. The irreducible open-subvariety dimension
theorem then applies.

The closed boundary has strictly smaller dimension: a longest chain in the
boundary extends strictly by an irreducible component of the closure. Translation
invariance puts the entire closure of every boundary orbit in that boundary.
Consequently the actual orbit through a point of minimal orbit dimension is
closed. No connectedness or separability hypothesis is used.

This proves the minimal-orbit part of Borel, *Linear Algebraic Groups*, §1.8,
used in §11.1. The separate orbit–stabilizer dimension comparison needed to
deduce minimal orbit dimension from maximal stabilizer dimension is not assumed
or asserted here. Source: `refs/KGroup/Bor1/Chapter1.tex`, Proposition 1.8, and
`refs/KGroup/Bor1/Chapter4.tex`, proof of Theorem 11.1.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Topology
open Theory.AlgebraicGroup.Variety.Geometric

universe u

private theorem closed_dimension_lt_of_component_escape
    {Y : Type u} [TopologicalSpace Y] [Nonempty Y]
    {B : Set Y} (hB : IsClosed B)
    (hfinite : topologicalKrullDim Y < ⊤)
    (hescape : ∀ Z ∈ irreducibleComponents Y, ¬ Z ⊆ B) :
    topologicalKrullDim B < topologicalKrullDim Y := by
  classical
  let : Nonempty (IrreducibleCloseds Y) :=
    ⟨⟨closure {Classical.choice (inferInstance : Nonempty Y)},
      isIrreducible_singleton.closure, isClosed_closure⟩⟩
  let : FiniteDimensionalOrder (IrreducibleCloseds Y) :=
    Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mpr
      ⟨ne_of_gt Order.bot_lt_krullDim, ne_of_lt hfinite⟩
  cases isEmpty_or_nonempty B with
  | inl h =>
    let : IsEmpty (IrreducibleCloseds B) :=
      ⟨fun C => h.false C.isIrreducible.nonempty.choose⟩
    exact Order.krullDim_eq_bot.trans_lt Order.bot_lt_krullDim
  | inr h =>
    let : Nonempty (IrreducibleCloseds B) :=
      ⟨⟨closure {Classical.choice h}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have hBfinite : topologicalKrullDim B < ⊤ :=
      (topologicalKrullDim_subspace_le Y B).trans_lt hfinite
    let : FiniteDimensionalOrder (IrreducibleCloseds B) :=
      Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mpr
        ⟨ne_of_gt Order.bot_lt_krullDim, ne_of_lt hBfinite⟩
    let p := LTSeries.longestOf (IrreducibleCloseds B)
    let m : IrreducibleCloseds B → IrreducibleCloseds Y :=
      IrreducibleCloseds.map Subtype.val continuous_subtype_val
    have hm : StrictMono m :=
      IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal
    let q := p.map m fun _ _ h => hm h
    obtain ⟨Z, hZ, hqZ⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible
        (q.last : Set Y) q.last.isIrreducible
    let C : IrreducibleCloseds Y :=
      ⟨Z, hZ.1, isClosed_of_mem_irreducibleComponents Z hZ⟩
    have hlt : q.last < C := by
      apply lt_of_le_of_ne hqZ
      intro heq
      apply hescape Z hZ
      have hlast : (q.last : Set Y) ⊆ B := by
        change closure (Subtype.val '' (p.last : Set B)) ⊆ B
        exact closure_minimal (by rintro _ ⟨b, _, rfl⟩; exact b.2) hB
      exact heq ▸ hlast
    have hlen := LTSeries.longestOf_is_longest (q.snoc C hlt)
    have hnat : p.length < (LTSeries.longestOf (IrreducibleCloseds Y)).length :=
      Nat.lt_of_succ_le hlen
    rw [topologicalKrullDim, topologicalKrullDim,
      Order.krullDim_eq_length_of_finiteDimensionalOrder,
      Order.krullDim_eq_length_of_finiteDimensionalOrder]
    exact_mod_cast hnat

namespace Theory.AlgebraicGroup.Variety.Geometric

variable {k : Type u} [Field k]

private theorem ltSeries_length_le_component_dimension
    (V : Geometric k) (p : LTSeries (IrreducibleCloseds V.toScheme))
    (Z : IrreducibleComponent V) (hpZ : (p.last : Set V.toScheme) ⊆ Z.1) :
    (p.length : WithBot ℕ∞) ≤
      dimension (irreducibleComponentSubvariety V Z).toGeometric := by
  let C := irreducibleComponentSubvariety V Z
  have hsub (i : Fin (p.length + 1)) :
      (p i : Set V.toScheme) ⊆ Set.range C.inclusion.hom := by
    rw [irreducibleComponentSubvariety_range]
    intro z hz
    exact hpZ (p.monotone (Fin.le_last i) hz)
  have hirr (i : Fin (p.length + 1)) :
      _root_.IsIrreducible (C.inclusion.hom ⁻¹' (p i : Set V.toScheme)) := by
    let e := C.inclusion.hom.isClosedEmbedding.isEmbedding.homeomorphOfSubsetRange (hsub i)
    let : IrreducibleSpace (p i : Set V.toScheme) := Subtype.irreducibleSpace (p i).isIrreducible
    exact isIrreducible_iff_irreducibleSpace.mpr (e.irreducibleSpace_iff.mpr inferInstance)
  let r (i : Fin (p.length + 1)) : IrreducibleCloseds C.toGeometric.toScheme :=
    ⟨C.inclusion.hom ⁻¹' (p i : Set V.toScheme), hirr i,
      (p i).isClosed.preimage C.inclusion.hom.continuous⟩
  have hr : StrictMono r := by
    intro i j hij
    apply lt_of_le_of_ne (Set.preimage_mono (p.monotone hij.le))
    intro heq
    have himage := congrArg (fun S : Set C.toGeometric.toScheme =>
      C.inclusion.hom '' S) heq
    change C.inclusion.hom '' (C.inclusion.hom ⁻¹' (p i : Set V.toScheme)) =
      C.inclusion.hom '' (C.inclusion.hom ⁻¹' (p j : Set V.toScheme)) at himage
    rw [Set.image_preimage_eq_of_subset (hsub i),
      Set.image_preimage_eq_of_subset (hsub j)] at himage
    exact (p.strictMono hij).ne (SetLike.coe_injective himage)
  exact Order.LTSeries.length_le_krullDim (LTSeries.mk p.length r hr)

/-- A dense open subset of a geometric variety has the same dimension, without an irreducibility assumption. -/
public theorem dimension_eq_denseOpen (V : Geometric k) (U : V.toScheme.Opens)
    (hdense : Dense (U : Set V.toScheme)) :
    dimension V = topologicalKrullDim U := by
  apply le_antisymm _ (topologicalKrullDim_subspace_le _ _)
  change Order.krullDim (IrreducibleCloseds V.toScheme) ≤ _
  refine iSup_le fun p => ?_
  obtain ⟨Z, hZ, hpZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (p.last : Set V.toScheme) p.last.isIrreducible
  let Z' : IrreducibleComponent V := ⟨Z, hZ⟩
  let C := irreducibleComponentSubvariety V Z'
  have hpdim := ltSeries_length_le_component_dimension V p Z' hpZ
  let CU : C.toGeometric.toScheme.Opens := ⟨C.inclusion.hom ⁻¹' U,
    U.2.preimage C.inclusion.hom.continuous⟩
  have hCU : (CU : Set C.toGeometric.toScheme).Nonempty := by
    obtain ⟨W, hWopen, hWne, hWZ⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
    obtain ⟨z, hzW, hzU⟩ := hdense.inter_open_nonempty W hWopen hWne
    have hzC : z ∈ Set.range C.inclusion.hom := by
      rw [irreducibleComponentSubvariety_range]
      exact hWZ hzW
    obtain ⟨c, rfl⟩ := hzC
    exact ⟨c, hzU⟩
  have hdim := dimension_eq_nonemptyOpen C.toGeometric CU hCU
  let j : CU → U := fun c => ⟨C.inclusion.hom c.1, c.2⟩
  have hj : IsEmbedding j :=
    (C.inclusion.hom.isClosedEmbedding.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict _ _
  exact hpdim.trans (hdim.trans_le hj.isInducing.topologicalKrullDim_le)

end Theory.AlgebraicGroup.Variety.Geometric

namespace Theory.AlgebraicGroup.Variety.Geometric.MorphicAction

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
variable {X : Geometric k} (A : MorphicAction G X) (x : Point X)

/-- The ambient boundary is the orbit closure minus the actual scheme-point orbit. -/
public theorem orbitBoundary_eq_sdiff :
    A.orbitBoundary x = Set.range (A.orbitMorphismRangeClosure x).inclusion.hom \
      Set.range (A.orbitMorphismAt x).hom := by rfl

/-- Inside its closure, the boundary is the complement of the factored orbit range. -/
public theorem orbitBoundaryInClosure_eq_compl :
    A.orbitBoundaryInClosure x =
      (Set.range (A.orbitMorphismAt x).toSchemeTheoreticRangeClosure.hom)ᶜ := by rfl

/-- The whole boundary has smaller dimension than the orbit closure, including for disconnected groups. -/
public theorem orbitBoundaryInClosure_dimension_lt :
    topologicalKrullDim (A.orbitBoundaryInClosure x) <
      dimension (A.orbitMorphismRangeClosure x).toGeometric := by
  let f := A.orbitMorphismAt x
  let C := A.orbitMorphismRangeClosure x
  let : Nonempty C.toGeometric.toScheme :=
    ⟨f.toSchemeTheoreticRangeClosure.hom
      (((affinePointEquiv G).symm 1).1 (IsLocalRing.closedPoint k))⟩
  apply closed_dimension_lt_of_component_escape
    (A.orbitBoundaryInClosure_isClosed x) (dimension_lt_top C.toGeometric)
  intro Z hZ hsub
  obtain ⟨U, hUopen, hUne, hUZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  obtain ⟨z, hzU, hzrange⟩ :=
    f.denseRange_toSchemeTheoreticRangeClosure.inter_open_nonempty U hUopen hUne
  exact hsub (hUZ hzU) hzrange

/-- The boundary of the selected orbit is invariant under every group translation. -/
public theorem translationMorphism_image_orbitBoundary (g : Theory.AlgebraicGroup.Variety.Point G) :
    (A.translationMorphism g).hom '' A.orbitBoundary x = A.orbitBoundary x := by
  change (A.translationMorphism g).hom ''
    (Set.range (A.orbitMorphismRangeClosure x).inclusion.hom \
      Set.range (A.orbitMorphismAt x).hom) = _
  have hinj : Function.Injective (A.translationMorphism g).hom :=
    (Scheme.homeoOfIso (A.translationIso g)).injective
  rw [Set.image_sdiff hinj,
    A.translationMorphism_image_orbitMorphismRangeClosure,
    A.translationMorphism_image_orbitMorphismAt_range]
  rfl

/-- The closure of an orbit through a rational boundary point stays in the same boundary. -/
public theorem orbitRangeClosure_subset_boundary_of_mem (y : Point X)
    (hy : y.1 (IsLocalRing.closedPoint k) ∈ A.orbitBoundary x) :
    Set.range (A.orbitMorphismRangeClosure y).inclusion.hom ⊆ A.orbitBoundary x := by
  let : MulAction (Theory.AlgebraicGroup.Variety.Point G) (Point X) := A.toMulAction
  rw [← A.orbitSupport_closure_eq_orbitMorphismRangeClosure_range y]
  apply closure_minimal _ (A.orbitBoundary_isClosed x)
  rw [A.orbitSupport_eq_rationalPointSupport_range,
    rationalPointSupport_eq_closedPoint_image]
  rintro z ⟨q, ⟨g, rfl⟩, rfl⟩
  change (A.toMulAction.smul g y).1 (IsLocalRing.closedPoint k) ∈ A.orbitBoundary x
  have hz : (A.translationMorphism g).hom (y.1 (IsLocalRing.closedPoint k)) ∈
      (A.translationMorphism g).hom '' A.orbitBoundary x := ⟨_, hy, rfl⟩
  rw [A.translationMorphism_image_orbitBoundary] at hz
  exact A.translationMorphism_hom_closedPoint g y ▸ hz

/-- The ambient orbit boundary pulls back to the boundary inside its closure. -/
public theorem orbitBoundary_preimage_inclusion :
    (A.orbitMorphismRangeClosure x).inclusion.hom ⁻¹' A.orbitBoundary x =
      A.orbitBoundaryInClosure x := by
  let f := A.orbitMorphismAt x
  let C := A.orbitMorphismRangeClosure x
  have hcomp := f.toSchemeTheoreticRangeClosure_comp_inclusion
  ext z
  change (C.inclusion.hom z ∈ Set.range C.inclusion.hom ∧
    C.inclusion.hom z ∉ Set.range f.hom) ↔
      z ∉ Set.range f.toSchemeTheoreticRangeClosure.hom
  have hrange : C.inclusion.hom z ∈ Set.range f.hom ↔
      z ∈ Set.range f.toSchemeTheoreticRangeClosure.hom := by
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨w, C.inclusion.hom.isClosedEmbedding.injective ?_⟩
      exact (congrArg (fun q => q w) hcomp).trans hw
    · rintro ⟨w, rfl⟩
      exact ⟨w, (congrArg (fun q => q w) hcomp).symm⟩
  simp only [Set.mem_range_self, true_and, hrange]

/-- The ambient boundary has strictly smaller dimension than the selected orbit closure. -/
public theorem orbitBoundary_dimension_lt :
    topologicalKrullDim (A.orbitBoundary x) <
      dimension (A.orbitMorphismRangeClosure x).toGeometric := by
  let C := A.orbitMorphismRangeClosure x
  have heq : C.inclusion.hom '' A.orbitBoundaryInClosure x = A.orbitBoundary x := by
    rw [← A.orbitBoundary_preimage_inclusion x, Set.image_preimage_eq_of_subset]
    exact Set.sdiff_subset
  have hdim := (C.inclusion.hom.isClosedEmbedding.isEmbedding.homeomorphImage
    (A.orbitBoundaryInClosure x)).isHomeomorph.topologicalKrullDim_eq
  rw [heq] at hdim
  rw [← hdim]
  exact A.orbitBoundaryInClosure_dimension_lt x

/-- An orbit through a rational boundary point has a strictly smaller closure dimension. -/
public theorem orbitRangeClosure_dimension_lt_of_mem_boundary (y : Point X)
    (hy : y.1 (IsLocalRing.closedPoint k) ∈ A.orbitBoundary x) :
    dimension (A.orbitMorphismRangeClosure y).toGeometric <
      dimension (A.orbitMorphismRangeClosure x).toGeometric := by
  let Cy := A.orbitMorphismRangeClosure y
  let f : Cy.toGeometric.toScheme → A.orbitBoundary x :=
    fun z => ⟨Cy.inclusion.hom z, A.orbitRangeClosure_subset_boundary_of_mem x y hy ⟨z, rfl⟩⟩
  have hf : IsEmbedding f :=
    Cy.inclusion.hom.isClosedEmbedding.isEmbedding.codRestrict _ _
  exact hf.isInducing.topologicalKrullDim_le.trans_lt
    (A.orbitBoundary_dimension_lt x)

/-- Minimality of the selected orbit closure dimension implies closedness of its actual scheme-point range. -/
public theorem isClosed_orbitMorphismAt_range_of_minimal_closure_dimension
    (hmin : ∀ y : Point X, dimension (A.orbitMorphismRangeClosure x).toGeometric ≤
      dimension (A.orbitMorphismRangeClosure y).toGeometric) :
    IsClosed (Set.range (A.orbitMorphismAt x).hom) := by
  by_contra hnot
  have hboundary : (A.orbitBoundary x).Nonempty := by
    change (Set.range (A.orbitMorphismRangeClosure x).inclusion.hom \
      Set.range (A.orbitMorphismAt x).hom).Nonempty
    rw [Set.sdiff_nonempty]
    intro hsub
    apply hnot
    have heq : Set.range (A.orbitMorphismAt x).hom =
        Set.range (A.orbitMorphismRangeClosure x).inclusion.hom := by
      apply Set.Subset.antisymm _ hsub
      rw [A.orbitMorphismRangeClosure_range]
      exact subset_closure
    rw [heq]
    exact (A.orbitRangeClosureSupport x).isClosed
  let : JacobsonSpace X.toScheme :=
    LocallyOfFiniteType.jacobsonSpace X.structureMap
  obtain ⟨z, hzB, hzclosed⟩ := nonempty_inter_closedPoints hboundary
    (A.orbitBoundary_isClosed x).isLocallyClosed
  let y : Point X := (pointEquivClosedPoint X.structureMap).symm ⟨z, hzclosed⟩
  have hy : y.1 (IsLocalRing.closedPoint k) = z :=
    congrArg Subtype.val ((pointEquivClosedPoint X.structureMap).apply_symm_apply
      ⟨z, hzclosed⟩)
  exact (not_lt_of_ge (hmin y)) (A.orbitRangeClosure_dimension_lt_of_mem_boundary x y (hy ▸ hzB))

/-- The locally closed orbit carrier and its reduced closure have equal dimension. -/
public theorem orbitSubvariety_dimension_eq_rangeClosure :
    dimension (A.orbitSubvariety x).toGeometric =
      dimension (A.orbitMorphismRangeClosure x).toGeometric := by
  let f := A.orbitMorphismAt x
  let C := f.schemeTheoreticRangeClosure
  let U : C.toGeometric.toScheme.Opens :=
    ⟨Set.range f.toSchemeTheoreticRangeClosure.hom, A.orbitRangeClosure_range_isOpen x⟩
  have hdimC := dimension_eq_denseOpen C.toGeometric U
    f.denseRange_toSchemeTheoreticRangeClosure
  have himage : C.inclusion.hom '' (U : Set C.toGeometric.toScheme) = Set.range f.hom := by
    change C.inclusion.hom '' Set.range f.toSchemeTheoreticRangeClosure.hom = _
    rw [← Set.range_comp]
    exact congrArg Set.range (congrArg (fun m : (ofAffine G).toScheme ⟶ X.toScheme =>
      (m : (ofAffine G).toScheme → X.toScheme))
      f.toSchemeTheoreticRangeClosure_comp_inclusion)
  have hdimU := (C.inclusion.hom.isClosedEmbedding.isEmbedding.homeomorphImage
    (U : Set C.toGeometric.toScheme)).isHomeomorph.topologicalKrullDim_eq
  rw [himage] at hdimU
  have hdimO := (A.orbitSubvariety x).inclusion.hom.isEmbedding.toHomeomorph.isHomeomorph
    |>.topologicalKrullDim_eq
  rw [A.orbitSubvariety_range] at hdimO
  exact hdimO.trans (hdimC.trans hdimU).symm

/-- An orbit in the boundary has strictly smaller dimension than the selected orbit. -/
public theorem orbitSubvariety_dimension_lt_of_mem_boundary (y : Point X)
    (hy : y.1 (IsLocalRing.closedPoint k) ∈ A.orbitBoundary x) :
    dimension (A.orbitSubvariety y).toGeometric < dimension (A.orbitSubvariety x).toGeometric := by
  rw [A.orbitSubvariety_dimension_eq_rangeClosure, A.orbitSubvariety_dimension_eq_rangeClosure]
  exact A.orbitRangeClosure_dimension_lt_of_mem_boundary x y hy

/-- An orbit of minimal dimension is closed (Borel, Proposition 1.8). -/
public theorem isClosed_orbitMorphismAt_range_of_minimal_dimension
    (hmin : ∀ y : Point X, dimension (A.orbitSubvariety x).toGeometric ≤
      dimension (A.orbitSubvariety y).toGeometric) :
    IsClosed (Set.range (A.orbitMorphismAt x).hom) := by
  apply A.isClosed_orbitMorphismAt_range_of_minimal_closure_dimension x
  intro y
  simpa only [← A.orbitSubvariety_dimension_eq_rangeClosure] using hmin y

end Theory.AlgebraicGroup.Variety.Geometric.MorphicAction
