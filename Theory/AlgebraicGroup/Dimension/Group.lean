module

public import Theory.AlgebraicGroup.Dimension.ClosedSubvariety

universe u

/-! Dimension and irreducible components of algebraic groups -/

namespace Theory.AlgebraicGroup

open scoped TensorProduct Cardinal

open LinearMap Submodule

variable {k : Type u} [Field k]

/-- The identity component, viewed as a closed subset of an algebraic group,
is irreducible. -/
public theorem identityComponent_isIrreducible
    (G : Variety k) [AlgebraicGroup G] :
    IsIrreducible (Theory.AlgebraicGroup.identityComponent G) := by
  let H := Theory.AlgebraicGroup.identityComponentClosedSubgroup G
  let G₀ : Variety k := H.carrierVariety
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  have hHconn : _root_.IsConnected (H : Set (Variety.Point G)) := by
    have hHcarrier : (H : Set (Variety.Point G)) =
        Theory.AlgebraicGroup.identityComponent G := by
      ext x
      rfl
    rw [hHcarrier]
    exact Theory.AlgebraicGroup.identityComponent_isConnected G
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.connectedSpace hHconn
  let : ConnectedSpace (Variety.Point G₀) :=
    e.connectedSpace_iff.mpr inferInstance
  have hG₀conn : Variety.IsConnected G₀ :=
    connectedSpace_iff_univ.mp inferInstance
  have hG₀irr : IsIrreducible (Set.univ : Set (Variety.Point G₀)) :=
    connectedAlgebraicGroup_irreducible G₀ hG₀conn
  have himage := hG₀irr.image
    (fun x : Variety.Point G₀ => (H.pointEquiv x).1)
    (H.inclusion.toVariety.continuous.continuousOn)
  have hrange : (fun x : Variety.Point G₀ =>
      (H.pointEquiv x).1) '' Set.univ =
      Theory.AlgebraicGroup.identityComponent G := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact (H.pointEquiv y).2
    · intro hx
      exact ⟨H.pointEquiv.symm ⟨x, hx⟩,
        Set.mem_univ _, by simp⟩
  rwa [hrange] at himage

/-- The identity component is the irreducible component containing the
identity point. -/
public theorem identityComponent_mem_irreducibleComponents
    (G : Variety k) [AlgebraicGroup G] :
    Theory.AlgebraicGroup.identityComponent G ∈
      irreducibleComponents (Variety.Point G) := by
  refine ⟨Theory.AlgebraicGroup.identityComponent_isIrreducible G, ?_⟩
  intro C hC hG₀C
  exact hC.isConnected.subset_connectedComponent
    (hG₀C (Theory.AlgebraicGroup.one_mem_identityComponent G))

/-- Every irreducible component of an algebraic group is a left translate of
the identity component. -/
public theorem irreducibleComponent_eq_leftCoset_identityComponent
    (G : Variety k) [AlgebraicGroup G]
    {C : Set (Variety.Point G)}
    (hC : C ∈ irreducibleComponents (Variety.Point G))
    (g : Variety.Point G) (hg : g ∈ C) :
    C = Set.image (fun x : Variety.Point G => g * x)
      (Theory.AlgebraicGroup.identityComponent G) := by
  let L : Set (Variety.Point G) := Set.image
    (fun x : Variety.Point G => g * x) (Theory.AlgebraicGroup.identityComponent G)
  have hCL : C ⊆ L := by
    have hsub := hC.1.isConnected.subset_connectedComponent hg
    rw [connectedComponent_eq_leftCoset G g] at hsub
    simpa [L, Theory.AlgebraicGroup.identityComponentSubgroup_carrier] using hsub
  have hLirr : IsIrreducible L := by
    have himage := (Theory.AlgebraicGroup.identityComponent_isIrreducible G).image
      (Theory.AlgebraicGroup.leftMulMorphism G g).toFun
      (Theory.AlgebraicGroup.leftMulMorphism G g).continuous.continuousOn
    simpa [L, Theory.AlgebraicGroup.leftMulMorphism_apply] using himage
  exact Set.Subset.antisymm hCL (hC.2 hLirr hCL)

/-- All irreducible components of an algebraic group have the dimension of
the identity component. -/
public theorem componentDimension_eq_identityComponent
    (G : Variety k) [AlgebraicGroup G]
    {C : Set (Variety.Point G)}
    (hC : C ∈ irreducibleComponents (Variety.Point G)) :
    Variety.componentDimension G C hC =
      Variety.componentDimension G (Theory.AlgebraicGroup.identityComponent G)
        (Theory.AlgebraicGroup.identityComponent_mem_irreducibleComponents G) := by
  classical
  let hCz : IsZariskiClosed G C := Variety.isClosed_iff_isZariskiClosed.mp
    (isClosed_of_mem_irreducibleComponents C hC)
  let hG₀z := Theory.AlgebraicGroup.identityComponent_isClosed G
  let g : Variety.Point G := hC.1.1.some
  have hg : g ∈ C := hC.1.1.some_mem
  have hCeq := Theory.AlgebraicGroup.irreducibleComponent_eq_leftCoset_identityComponent
    G hC g hg
  let f₀ := Theory.AlgebraicGroup.leftMulMorphism G g
  let f₁ := Theory.AlgebraicGroup.leftMulMorphism G g⁻¹
  have hf₀ : ∀ x, x ∈ Theory.AlgebraicGroup.identityComponent G → f₀.toFun x ∈ C := by
    intro x hx
    rw [hCeq]
    exact ⟨x, hx, by simp [f₀, Theory.AlgebraicGroup.leftMulMorphism_apply]⟩
  have hf₁ : ∀ x, x ∈ C → f₁.toFun x ∈ Theory.AlgebraicGroup.identityComponent G := by
    intro x hx
    rw [hCeq] at hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa [f₁, Theory.AlgebraicGroup.leftMulMorphism_apply] using hy
  let F := f₀.restrictClosedSubvariety hG₀z hCz hf₀
  let I := f₁.restrictClosedSubvariety hCz hG₀z hf₁
  have hIF : ∀ x, I.toFun (F.toFun x) = x := by
    intro x
    apply (Variety.closedSubvarietyPointEquiv hG₀z).injective
    apply Subtype.ext
    rw [Variety.Morphism.restrictClosedSubvariety_apply,
      Variety.Morphism.restrictClosedSubvariety_apply]
    simp [f₀, f₁, Theory.AlgebraicGroup.leftMulMorphism_apply]
  have hFI : ∀ x, F.toFun (I.toFun x) = x := by
    intro x
    apply (Variety.closedSubvarietyPointEquiv hCz).injective
    apply Subtype.ext
    rw [Variety.Morphism.restrictClosedSubvariety_apply,
      Variety.Morphism.restrictClosedSubvariety_apply]
    simp [f₀, f₁, Theory.AlgebraicGroup.leftMulMorphism_apply]
  let e := coordinateRingAlgEquivOfInverseMorphisms F I hIF hFI
  let : IsDomain (coordinateRing (Variety.closedSubvariety hCz)) := by
    simpa [hCz] using isDomain_coordinateRing_component C hC
  let : IsDomain (coordinateRing (Variety.closedSubvariety hG₀z)) := by
    simpa [hG₀z] using isDomain_coordinateRing_component
      (Theory.AlgebraicGroup.identityComponent G)
      (Theory.AlgebraicGroup.identityComponent_mem_irreducibleComponents G)
  let eFrac : FractionRing (coordinateRing (Variety.closedSubvariety hCz)) ≃ₐ[k]
      FractionRing (coordinateRing (Variety.closedSubvariety hG₀z)) :=
    IsFractionRing.algEquivOfAlgEquiv e
  change Algebra.trdeg k (FractionRing (coordinateRing
      (Variety.closedSubvariety hCz))) =
    Algebra.trdeg k (FractionRing (coordinateRing
      (Variety.closedSubvariety hG₀z)))
  exact eFrac.trdeg_eq

/-- The geometric dimension of an algebraic group is the dimension of its
identity component, agreeing with Definition 1.1.5. -/
public theorem dimension_eq_identityComponent
    (G : Variety k) [AlgebraicGroup G] :
    Variety.dimension G =
      Variety.componentDimension G (Theory.AlgebraicGroup.identityComponent G)
        (Theory.AlgebraicGroup.identityComponent_mem_irreducibleComponents G) := by
  classical
  let I := {C : Set (Variety.Point G) //
    C ∈ irreducibleComponents (Variety.Point G)}
  let G₀ : I := ⟨Theory.AlgebraicGroup.identityComponent G,
    Theory.AlgebraicGroup.identityComponent_mem_irreducibleComponents G⟩
  unfold Variety.dimension
  change (⨆ C : I, Variety.componentDimension G C.1 C.2) = _
  apply le_antisymm
  · apply ciSup_le'
    intro C
    exact (Theory.AlgebraicGroup.componentDimension_eq_identityComponent G C.2).le
  · have hb : BddAbove (Set.range
        (fun C : I => Variety.componentDimension G C.1 C.2)) :=
      ⟨Cardinal.mk G.Coordinates, by
        intro x hx
        rcases hx with ⟨C, rfl⟩
        exact componentDimension_le_coordinates G C.1 C.2⟩
    simpa [G₀] using
      (le_ciSup hb G₀)

/-- The closed-subgroup variety carried by the identity component has the
same dimension as the whole algebraic group. -/
public theorem dimension_identityComponentClosedSubgroup
    (G : Variety k) [AlgebraicGroup G] :
    Variety.dimension
        (Theory.AlgebraicGroup.identityComponentClosedSubgroup G).carrierVariety =
      Variety.dimension G := by
  let H := Theory.AlgebraicGroup.identityComponentClosedSubgroup G
  let hG₀z := Theory.AlgebraicGroup.identityComponent_isClosed G
  have hG₀i := Theory.AlgebraicGroup.identityComponent_isIrreducible G
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  have hHcarrier : (H : Set (Variety.Point G)) =
      Theory.AlgebraicGroup.identityComponent G := by
    ext x
    rfl
  have hHirr : IsIrreducible (H : Set (Variety.Point G)) := by
    rw [hHcarrier]
    exact hG₀i
  let : IrreducibleSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.irreducibleSpace hHirr
  let : IrreducibleSpace (Variety.Point H.carrierVariety) :=
    e.irreducibleSpace_iff.mpr inferInstance
  have hHuniv : IsIrreducible
      (Set.univ : Set (Variety.Point H.carrierVariety)) :=
    IrreducibleSpace.isIrreducible_univ _
  rw [dimension_eq_fractionRing_of_isIrreducible H.carrierVariety hHuniv,
    Theory.AlgebraicGroup.dimension_eq_identityComponent G]
  change Algebra.trdeg k (FractionRing (coordinateRing H.carrierVariety)) =
    Algebra.trdeg k (FractionRing
      (coordinateRing (Variety.closedSubvariety hG₀z)))
  rfl

end Theory.AlgebraicGroup
