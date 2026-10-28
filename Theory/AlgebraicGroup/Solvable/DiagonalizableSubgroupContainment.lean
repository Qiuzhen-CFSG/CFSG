module

public import Theory.AlgebraicGroup.Solvable.TriangularDiagonalizableSplitting

/-!
# Diagonalizable subgroups of connected solvable closed subgroups

This module proves the connected-solvable case of GLS3, Theorem 1.5.1:
if a diagonalizable closed subgroup `S` lies in a connected solvable closed
subgroup `H`, then `S` lies in a closed subtorus of `H`.

The proof first regards `S` as a closed subgroup of the algebraic group
`H.carrierVariety`.  Its carrier is unchanged up to an explicit closed-image
isomorphism, so diagonalizability is preserved without assuming that `S` is
connected.  Lie--Kolchin supplies a triangular presentation of `H`; the
triangular diagonalizable-splitting theorem then constructs the desired torus
inside `H`.  Finally, the inclusion of `H` maps this torus back to the
ambient group.  Closed images of tori are tori, and the two required
containments follow directly from the image descriptions.

The triangular splitting input is the characteristic-free form of Borel,
*Linear Algebraic Groups*, Chapter III, Theorem 10.6(5).  No maximal-torus
conjugacy theorem is used.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option linter.style.haveILetI false

omit [IsAlgClosed k] in
private lemma closedSubgroup_carrier_isConnected_local
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace
      {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

private noncomputable def closedSubgroupInside
    {G : Variety k} [AlgebraicGroup G]
    (K H : ClosedSubgroup G) (hKH : K ≤ H) :
    ClosedSubgroup H.carrierVariety := by
  let f : AlgebraicGroup.Morphism K.carrierVariety H.carrierVariety :=
    K.inclusion.codRestrictClosedSubgroup H
      (fun x ↦ hKH (K.pointEquiv x).property)
  exact f.imageClosedSubgroup

private theorem mem_closedSubgroupInside_iff
    {G : Variety k} [AlgebraicGroup G]
    (K H : ClosedSubgroup G) (hKH : K ≤ H)
    (x : Variety.Point H.carrierVariety) :
    letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
    x ∈ closedSubgroupInside K H hKH ↔ H.includePoint x ∈ K := by
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  let f : AlgebraicGroup.Morphism K.carrierVariety H.carrierVariety :=
    K.inclusion.codRestrictClosedSubgroup H
      (fun y ↦ hKH (K.pointEquiv y).property)
  have hf (y : Variety.Point K.carrierVariety) :
      H.inclusion.onPoints (f.onPoints y) = K.inclusion.onPoints y :=
    K.inclusion.codRestrictClosedSubgroup_inclusion_apply H
      (fun z ↦ hKH (K.pointEquiv z).property) y
  change (∃ y, f.onPoints y = x) ↔ H.includePoint x ∈ K
  constructor
  · rintro ⟨y, rfl⟩
    change H.inclusion.onPoints (f.onPoints y) ∈ K
    rw [hf]
    exact (K.pointEquiv y).property
  · intro hx
    let y : Variety.Point K.carrierVariety :=
      K.pointEquiv.symm ⟨H.includePoint x, hx⟩
    refine ⟨y, H.inclusion_injective ?_⟩
    rw [hf]
    exact congrArg Subtype.val
      (K.pointEquiv.apply_symm_apply ⟨H.includePoint x, hx⟩)

private theorem closedSubgroupInside_isDiagonalizable
    {G : Variety k} [AlgebraicGroup G]
    (S H : ClosedSubgroup G) (hSH : S ≤ H)
    (hS : IsDiagonalizableClosedSubgroup S) :
    letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
    IsDiagonalizableClosedSubgroup (closedSubgroupInside S H hSH) := by
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  let f : AlgebraicGroup.Morphism S.carrierVariety H.carrierVariety :=
    S.inclusion.codRestrictClosedSubgroup H
      (fun x ↦ hSH (S.pointEquiv x).property)
  have hf_inj : Function.Injective f.onPoints := by
    intro x y hxy
    apply S.inclusion_injective
    have := congrArg H.inclusion.onPoints hxy
    simpa [f, Morphism.codRestrictClosedSubgroup_inclusion_apply] using this
  have hf_coord : ∀ c : S.carrierVariety.Coordinates,
      ∃ q : Variety.PolynomialFunction H.carrierVariety,
        Variety.PolynomialFunction.pullback f.toVariety q =
          Variety.PolynomialFunction.ofPolynomial S.carrierVariety
            (MvPolynomial.X c) := by
    intro c
    refine ⟨Variety.PolynomialFunction.ofPolynomial H.carrierVariety
      (MvPolynomial.X c), ?_⟩
    apply Variety.PolynomialFunction.ext
    intro x
    change evalPolynomial (f.onPoints x).val (MvPolynomial.X c) =
      evalPolynomial x.val (MvPolynomial.X c)
    rw [evalPolynomial_X, evalPolynomial_X]
    have hx : H.inclusion.onPoints (f.onPoints x) = S.inclusion.onPoints x :=
      S.inclusion.codRestrictClosedSubgroup_inclusion_apply H
        (fun y ↦ hSH (S.pointEquiv y).property) x
    exact congrArg (fun z ↦ z.val c) hx
  change IsDiagonalizableClosedSubgroup f.imageClosedSubgroup
  letI : AlgebraicGroup f.imageClosedSubgroup.carrierVariety :=
    f.imageClosedSubgroup.carrierAlgebraicGroup
  obtain ⟨e, -⟩ :=
    f.iso_imageClosedSubgroup_of_coordinate_preimage hf_inj hf_coord
  obtain ⟨n, D, ⟨dIso⟩⟩ := hS
  letI : AlgebraicGroup D.carrierVariety := D.carrierAlgebraicGroup
  exact ⟨n, D, ⟨dIso.comp e.symm⟩⟩

/-- A diagonalizable closed subgroup lying in a connected solvable closed
subgroup is contained in a closed subtorus of that subgroup. -/
public theorem exists_subtorus_containing_diagonalizable_closedSubgroup_of_le_connected_solvable
    {G : Variety k} [AlgebraicGroup G]
    (H S : ClosedSubgroup G)
    (hHconnected : _root_.IsConnected (H : Set (Variety.Point G)))
    (hHsolvable : Group.IsSolvable (Variety.Point H.carrierVariety))
    (hS : IsDiagonalizableClosedSubgroup S)
    (hSH : S ≤ H) :
    ∃ T : ClosedSubgroup G, IsSubtorus T ∧ S ≤ T ∧ T ≤ H := by
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  let SI : ClosedSubgroup H.carrierVariety := closedSubgroupInside S H hSH
  have hSI : IsDiagonalizableClosedSubgroup SI :=
    closedSubgroupInside_isDiagonalizable S H hSH hS
  have hHvar : Variety.IsConnected H.carrierVariety :=
    closedSubgroup_carrier_isConnected_local H hHconnected
  obtain ⟨n, hn, HT, ⟨e⟩⟩ :=
    exists_iso_closedSubgroup_tVariety_of_isSolvable_isConnected
      hHsolvable hHvar
  let P : TriangularPresentation H.carrierVariety :=
    { n := n, positive := hn, subgroup := HT, iso := e }
  obtain ⟨TI, hTI, hSITI⟩ :=
    P.exists_subtorus_containing_diagonalizableClosedSubgroup_of_solvable_connected
      hHsolvable hHvar SI hSI
  letI : AlgebraicGroup TI.carrierVariety := TI.carrierAlgebraicGroup
  let j : AlgebraicGroup.Morphism TI.carrierVariety G :=
    H.inclusion.comp TI.inclusion
  let T : ClosedSubgroup G := j.imageClosedSubgroup
  have hT : IsSubtorus T := morphism_image_isTorus j hTI
  have hST : S ≤ T := by
    intro x hxS
    have hxH : x ∈ H := hSH hxS
    let xH : Variety.Point H.carrierVariety := H.pointEquiv.symm ⟨x, hxH⟩
    have hxHval : H.includePoint xH = x := by
      exact congrArg Subtype.val (H.pointEquiv.apply_symm_apply ⟨x, hxH⟩)
    have hxSI : xH ∈ SI :=
      (mem_closedSubgroupInside_iff S H hSH xH).mpr (by
        rw [hxHval]
        exact hxS)
    have hxTI : xH ∈ TI := hSITI hxSI
    let xTI : Variety.Point TI.carrierVariety :=
      TI.pointEquiv.symm ⟨xH, hxTI⟩
    change x ∈ j.image
    refine ⟨xTI, ?_⟩
    change H.inclusion.onPoints (TI.inclusion.onPoints xTI) = x
    rw [← hxHval]
    exact congrArg H.inclusion.onPoints
      (congrArg Subtype.val (TI.pointEquiv.apply_symm_apply ⟨xH, hxTI⟩))
  have hTH : T ≤ H := by
    intro x hxT
    change x ∈ j.image at hxT
    obtain ⟨y, rfl⟩ := hxT
    exact (H.pointEquiv (TI.inclusion.onPoints y)).property
  exact ⟨T, hT, hST, hTH⟩

end Theory.AlgebraicGroup
