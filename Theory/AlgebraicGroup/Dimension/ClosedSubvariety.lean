module

public import Theory.AlgebraicGroup.Dimension.Product
public import Theory.AlgebraicGroup.Dimension.Quotient

universe u

/-! Closed subvarieties and their ambient irreducible components. -/

namespace Theory.AlgebraicGroup

open scoped TensorProduct Cardinal

open LinearMap Submodule

variable {k : Type u} [Field k]

/-- The vanishing ideal of a closed subvariety equals the vanishing ideal of
the corresponding closed set of the ambient variety. -/
public theorem vanishingIdeal_closedSubvariety {V : Variety k} {S : Set (Variety.Point V)}
    (hS : IsZariskiClosed V S) :
    vanishingIdeal (Set.univ : Set (Variety.Point (Variety.closedSubvariety hS))) = vanishingIdeal S := by
  ext p
  constructor
  · intro hp x hxS
    let y : Variety.Point (Variety.closedSubvariety hS) :=
      (Variety.closedSubvarietyPointEquiv hS).symm ⟨x, hxS⟩
    have hy : evalPolynomial y.val p = 0 := hp y (Set.mem_univ y)
    have hyx : y.val = x.val := by rfl
    rwa [hyx] at hy
  · intro hp y hyu
    let x : {x : Variety.Point V // x ∈ S} := Variety.closedSubvarietyPointEquiv hS y
    have hx : evalPolynomial x.1.val p = 0 := hp x.1 (by exact x.2)
    have hxy : x.1.val = y.val := by rfl
    rwa [hxy] at hx

/-- The vanishing ideal of a set of points of a closed subvariety equals the
vanishing ideal of its image in the ambient variety (the point spaces are
bijective with the same coordinate functions). -/
public theorem vanishingIdeal_closedSubvariety_image {V : Variety k}
    {S : Set (Variety.Point V)} (hS : IsZariskiClosed V S)
    (T : Set (Variety.Point (Variety.closedSubvariety hS))) :
    vanishingIdeal T = vanishingIdeal
      ((fun y : Variety.Point (Variety.closedSubvariety hS) =>
        (Variety.closedSubvarietyPointEquiv hS y).1) '' T) := by
  ext p
  constructor
  · intro hp x hx
    rcases hx with ⟨y, hyT, hy⟩
    subst x
    exact hp y hyT
  · intro hp y hyT
    exact hp (Variety.closedSubvarietyPointEquiv hS y).1 ⟨y, hyT, rfl⟩

/-- The image of an irreducible component of a closed subvariety in the
ambient variety is an irreducible closed subset. -/
public theorem component_image_isIrreducible_closed {V : Variety k}
    {S : Set (Variety.Point V)} (hS : IsZariskiClosed V S)
    {C : Set (Variety.Point (Variety.closedSubvariety hS))}
    (hC : C ∈ irreducibleComponents (Variety.Point (Variety.closedSubvariety hS))) :
    IsIrreducible ((fun y : Variety.Point (Variety.closedSubvariety hS) =>
        (Variety.closedSubvarietyPointEquiv hS y).1) '' C) ∧
    IsZariskiClosed V ((fun y : Variety.Point (Variety.closedSubvariety hS) =>
        (Variety.closedSubvarietyPointEquiv hS y).1) '' C) := by
  let W : Variety k := Variety.closedSubvariety hS
  let e : Variety.Point W → Variety.Point V := fun y => (Variety.closedSubvarietyPointEquiv hS y).1
  constructor
  · have hcont : ContinuousOn e C := by
      rw [continuousOn_iff_isClosed]
      intro Z hZ
      have hZz : IsZariskiClosed V Z := Variety.isClosed_iff_isZariskiClosed.mp hZ
      rcases hZz with ⟨E, hE⟩
      have hPre : IsClosed (C ∩ e ⁻¹' Z) := by
        rw [Variety.isClosed_iff_isZariskiClosed]
        refine isZariskiClosed_inter (Variety.isClosed_iff_isZariskiClosed.mp
          (isClosed_of_mem_irreducibleComponents C hC)) ?_
        refine ⟨E, ?_⟩
        ext y
        constructor
        · intro hy p hp
          have hy' : e y ∈ Z := hy
          rw [hE] at hy'
          have hy'' : evalPolynomial (e y).val p = 0 := hy' p hp
          have hyx : (Variety.closedSubvarietyPointEquiv hS y).1.val = y.val := by rfl
          simpa [e, hyx] using hy''
        · intro hy
          change e y ∈ Z
          rw [hE]
          change ∀ p ∈ E, evalPolynomial (e y).val p = 0
          intro p hp
          have hyx : (Variety.closedSubvarietyPointEquiv hS y).1.val = y.val := by rfl
          simpa [e, hyx] using hy p hp
      refine ⟨C ∩ e ⁻¹' Z, hPre, ?_⟩
      rw [Set.inter_assoc, Set.inter_comm, ← Set.inter_assoc, Set.inter_self]
    exact IsIrreducible.image hC.1 e hcont
  · have hzC : IsZariskiClosed W C := Variety.isClosed_iff_isZariskiClosed.mp
      (isClosed_of_mem_irreducibleComponents C hC)
    rcases hzC with ⟨E, hE⟩
    let Z : Set (Variety.Point V) := {x | ∀ p ∈ E, evalPolynomial x.val p = 0}
    have hZz : IsZariskiClosed V Z := ⟨E, rfl⟩
    have hEq : e '' C = S ∩ Z := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hyC, hy⟩
        have hyE : ∀ p ∈ E, evalPolynomial y.val p = 0 := by
          rw [hE] at hyC
          exact hyC
        constructor
        · rw [← hy]
          exact (Variety.closedSubvarietyPointEquiv hS y).2
        · intro p hp
          rw [← hy]
          have hyx : (Variety.closedSubvarietyPointEquiv hS y).1.val = y.val := by rfl
          simpa [e, hyx] using hyE p hp
      · intro hx
        rcases hx with ⟨hxS, hxZ⟩
        let y : Variety.Point W :=
          (Variety.closedSubvarietyPointEquiv hS).symm ⟨x, hxS⟩
        refine ⟨y, ?_, ?_⟩
        · rw [hE]
          change ∀ p ∈ E, evalPolynomial y.val p = 0
          intro p hp
          have hyx : y.val = x.val := by rfl
          simpa [y, hyx] using hxZ p hp
        · simp [e, y]
    rw [hEq]
    exact isZariskiClosed_inter hS hZz

public theorem closedSubvariety_dimension_le (V : Variety k) {S : Set (Variety.Point V)}
    (hS : IsZariskiClosed V S) :
    Variety.dimension (Variety.closedSubvariety hS) ≤ Variety.dimension V := by
  classical
  let W : Variety k := Variety.closedSubvariety hS
  let e : Variety.Point W → Variety.Point V := fun y => (Variety.closedSubvarietyPointEquiv hS y).1
  unfold Variety.dimension
  apply ciSup_le'
  intro C
  let C' : Set (Variety.Point V) := e '' C.1
  have hC'irr : IsIrreducible C' := by
    simpa [C', e] using (component_image_isIrreducible_closed hS C.2).1
  rcases exists_mem_irreducibleComponents_subset_of_isIrreducible C' hC'irr with ⟨D, hD, hC'D⟩
  have hle : Variety.componentDimension W C.1 C.2 ≤ Variety.componentDimension V D hD := by
    let hzC : IsZariskiClosed W C.1 := Variety.isClosed_iff_isZariskiClosed.mp
      (isClosed_of_mem_irreducibleComponents C.1 C.2)
    let hzD : IsZariskiClosed V D := Variety.isClosed_iff_isZariskiClosed.mp
      (isClosed_of_mem_irreducibleComponents D hD)
    have hICD : vanishingIdeal D ≤ vanishingIdeal C' := by
      intro p hp x hxC'
      exact hp x (hC'D hxC')
    have hq : Algebra.trdeg k (MvPolynomial V.Coordinates k ⧸ vanishingIdeal C') ≤
        Algebra.trdeg k (MvPolynomial V.Coordinates k ⧸ vanishingIdeal D) :=
      trdeg_le_of_quotient_le V.Coordinates (vanishingIdeal C') (vanishingIdeal D) hICD
    have hdomC : IsDomain (MvPolynomial V.Coordinates k ⧸ vanishingIdeal C') := by
      have hdom : IsDomain (coordinateRing (Variety.closedSubvariety hzC)) :=
        isDomain_coordinateRing_component C.1 C.2
      change IsDomain (MvPolynomial V.Coordinates k ⧸
        vanishingIdeal (Set.univ : Set (Variety.Point (Variety.closedSubvariety hzC)))) at hdom
      rw [vanishingIdeal_closedSubvariety (V := W) hzC] at hdom
      rw [vanishingIdeal_closedSubvariety_image hS] at hdom
      simpa [C', e] using hdom
    have hdomD : IsDomain (MvPolynomial V.Coordinates k ⧸ vanishingIdeal D) := by
      have hdom : IsDomain (coordinateRing (Variety.closedSubvariety hzD)) :=
        isDomain_coordinateRing_component D hD
      change IsDomain (MvPolynomial V.Coordinates k ⧸
        vanishingIdeal (Set.univ : Set (Variety.Point (Variety.closedSubvariety hzD)))) at hdom
      rw [vanishingIdeal_closedSubvariety hzD] at hdom
      exact hdom
    have hfracC : Algebra.trdeg k (FractionRing (MvPolynomial V.Coordinates k ⧸ vanishingIdeal C')) =
        Algebra.trdeg k (MvPolynomial V.Coordinates k ⧸ vanishingIdeal C') :=
      trdeg_fractionRing_eq (MvPolynomial V.Coordinates k ⧸ vanishingIdeal C')
    have hfracD : Algebra.trdeg k (FractionRing (MvPolynomial V.Coordinates k ⧸ vanishingIdeal D)) =
        Algebra.trdeg k (MvPolynomial V.Coordinates k ⧸ vanishingIdeal D) :=
      trdeg_fractionRing_eq (MvPolynomial V.Coordinates k ⧸ vanishingIdeal D)
    have hgoal : Algebra.trdeg k (FractionRing (MvPolynomial V.Coordinates k ⧸ vanishingIdeal C')) ≤
        Algebra.trdeg k (FractionRing (MvPolynomial V.Coordinates k ⧸ vanishingIdeal D)) := by
      rw [hfracC, hfracD]
      exact hq
    have hcompW : Variety.componentDimension W C.1 C.2 =
        Algebra.trdeg k (FractionRing (MvPolynomial V.Coordinates k ⧸ vanishingIdeal C')) := by
      have hc : Variety.componentDimension W C.1 C.2 =
          Algebra.trdeg k (FractionRing (coordinateRing (Variety.closedSubvariety hzC))) := by
        simp [Variety.componentDimension]
      rw [hc]
      change Algebra.trdeg k (FractionRing (MvPolynomial V.Coordinates k ⧸
        vanishingIdeal (Set.univ : Set (Variety.Point (Variety.closedSubvariety hzC))))) =
        Algebra.trdeg k (FractionRing (MvPolynomial V.Coordinates k ⧸ vanishingIdeal C'))
      rw [vanishingIdeal_closedSubvariety (V := W) hzC,
        vanishingIdeal_closedSubvariety_image hS]
    have hcompD : Variety.componentDimension V D hD =
        Algebra.trdeg k (FractionRing (MvPolynomial V.Coordinates k ⧸ vanishingIdeal D)) := by
      have hc : Variety.componentDimension V D hD =
          Algebra.trdeg k (FractionRing (coordinateRing (Variety.closedSubvariety hzD))) := by
        simp [Variety.componentDimension]
      rw [hc]
      change Algebra.trdeg k (FractionRing (MvPolynomial V.Coordinates k ⧸
        vanishingIdeal (Set.univ : Set (Variety.Point (Variety.closedSubvariety hzD))))) =
        Algebra.trdeg k (FractionRing (MvPolynomial V.Coordinates k ⧸ vanishingIdeal D))
      rw [vanishingIdeal_closedSubvariety hzD]
    rw [hcompW, hcompD]
    exact hgoal
  have hb : BddAbove (Set.range (fun D : {D : Set (Variety.Point V) //
      D ∈ irreducibleComponents (Variety.Point V)} => Variety.componentDimension V D.1 D.2)) := by
    exact ⟨Cardinal.mk V.Coordinates, by
      intro x hx
      rcases hx with ⟨D, rfl⟩
      exact componentDimension_le_coordinates V D.1 D.2⟩
  exact le_trans hle (le_ciSup hb ⟨D, hD⟩)

/-- For an irreducible variety, the unique irreducible component is the whole
point space, so its dimension is the transcendence degree of its coordinate
field. -/
public theorem dimension_eq_fractionRing_of_isIrreducible (V : Variety k)
    (h : IsIrreducible (Set.univ : Set (Variety.Point V))) :
    Variety.dimension V = Algebra.trdeg k (FractionRing (coordinateRing V)) := by
  let : IrreducibleSpace (Variety.Point V) := (irreducibleSpace_def _).mpr h
  unfold Variety.dimension
  let IV := {C : Set (Variety.Point V) //
    C ∈ irreducibleComponents (Variety.Point V)}
  let U : IV := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]
    exact Set.mem_singleton Set.univ⟩
  let : Subsingleton IV := ⟨by
    intro C D
    apply Subtype.ext
    have hC : C.1 = Set.univ := by
      let c : Set (Variety.Point V) := C.1
      have hC' : c ∈ irreducibleComponents (Variety.Point V) := C.2
      rw [irreducibleComponents_eq_singleton] at hC'
      exact hC'
    have hD : D.1 = Set.univ := by
      let d : Set (Variety.Point V) := D.1
      have hD' : d ∈ irreducibleComponents (Variety.Point V) := D.2
      rw [irreducibleComponents_eq_singleton] at hD'
      exact hD'
    rw [hC, hD]⟩
  change (⨆ C : IV, Variety.componentDimension V C.1 C.2) = _
  rw [ciSup_subsingleton U]
  unfold Variety.componentDimension
  change Algebra.trdeg k (FractionRing (MvPolynomial V.Coordinates k ⧸
    vanishingIdeal (Set.univ : Set (Variety.Point
      (Variety.closedSubvariety _))))) = _
  rw [vanishingIdeal_closedSubvariety]

/-- Passing a closed irreducible subset of a closed subvariety back to the
ambient variety does not change its dimension. -/
public theorem closedSubvariety_image_dimension_eq_of_isIrreducible
    {V : Variety k} {S : Set (Variety.Point V)}
    (hS : IsZariskiClosed V S)
    {T : Set (Variety.Point (Variety.closedSubvariety hS))}
    (hT : IsZariskiClosed (Variety.closedSubvariety hS) T)
    (hTi : IsIrreducible T) :
    let hI := closedSubvariety_image_isZariskiClosed hS hT
    Variety.dimension (Variety.closedSubvariety hT) =
      Variety.dimension (Variety.closedSubvariety hI) := by
  dsimp only
  let I := (fun y : Variety.Point (Variety.closedSubvariety hS) =>
    (Variety.closedSubvarietyPointEquiv hS y).1) '' T
  let hI : IsZariskiClosed V I := closedSubvariety_image_isZariskiClosed hS hT
  let inc : Variety.Point (Variety.closedSubvariety hS) → Variety.Point V :=
    fun y => (Variety.closedSubvarietyPointEquiv hS y).1
  have hinc : Continuous inc :=
    continuous_subtype_val.comp (Variety.closedSubvarietyPointHomeomorph hS).continuous
  have hIi : IsIrreducible I := by
    simpa [I, inc] using hTi.image inc hinc.continuousOn
  let eT := Variety.closedSubvarietyPointHomeomorph hT
  let : IrreducibleSpace {x : Variety.Point (Variety.closedSubvariety hS) // x ∈ T} :=
    Subtype.irreducibleSpace hTi
  let : IrreducibleSpace (Variety.Point (Variety.closedSubvariety hT)) :=
    eT.irreducibleSpace_iff.mpr inferInstance
  have hWTi : IsIrreducible
      (Set.univ : Set (Variety.Point (Variety.closedSubvariety hT))) :=
    IrreducibleSpace.isIrreducible_univ _
  let eI := Variety.closedSubvarietyPointHomeomorph hI
  let : IrreducibleSpace {x : Variety.Point V // x ∈ I} :=
    Subtype.irreducibleSpace hIi
  let : IrreducibleSpace (Variety.Point (Variety.closedSubvariety hI)) :=
    eI.irreducibleSpace_iff.mpr inferInstance
  have hWIi : IsIrreducible
      (Set.univ : Set (Variety.Point (Variety.closedSubvariety hI))) :=
    IrreducibleSpace.isIrreducible_univ _
  rw [dimension_eq_fractionRing_of_isIrreducible _ hWTi,
    dimension_eq_fractionRing_of_isIrreducible _ hWIi]
  change Algebra.trdeg k (FractionRing (MvPolynomial V.Coordinates k ⧸
      vanishingIdeal (Set.univ : Set (Variety.Point
        (Variety.closedSubvariety hT))))) =
    Algebra.trdeg k (FractionRing (MvPolynomial V.Coordinates k ⧸
      vanishingIdeal (Set.univ : Set (Variety.Point
        (Variety.closedSubvariety hI)))))
  rw [vanishingIdeal_closedSubvariety hT,
    vanishingIdeal_closedSubvariety hI,
    vanishingIdeal_closedSubvariety_image hS T]

end Theory.AlgebraicGroup
