module

public import Theory.AlgebraicGroup.Borel.Defs
public import Theory.AlgebraicGroup.ClosedSubgroup.Conjugation
public import Theory.AlgebraicGroup.Tori.Maximal
public import Theory.AlgebraicGroup.Unipotent.Radical

/-!
This module isolates `theorem_1_6_2_b` from `Theory.AlgebraicGroup.Borel.Conjugation`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

universe u

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

private lemma closedSubgroup_carrier_isConnected
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

private lemma closedSubgroup_isConnected_of_carrier
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : Variety.IsConnected H.carrierVariety) :
    _root_.IsConnected (H : Set (Variety.Point G)) := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    connectedSpace_iff_univ.mpr hH
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    e.connectedSpace_iff.mp inferInstance
  exact isConnected_iff_connectedSpace.mpr inferInstance

private lemma closedSubgroup_conjugate_isConnected
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    _root_.IsConnected (H.conjugate g : Set (Variety.Point G)) := by
  apply closedSubgroup_isConnected_of_carrier
  exact (algebraicGroupIso_isConnected_iff (H.conjugateIso g)).mp
    (closedSubgroup_carrier_isConnected H hH)

private lemma closedSubgroup_conjugate_isSolvable
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G)
    (hH : Group.IsSolvable (Variety.Point H.carrierVariety)) :
    Group.IsSolvable (Variety.Point (H.conjugate g).carrierVariety) := by
  let : Group.IsSolvable (Variety.Point H.carrierVariety) := hH
  exact Group.isSolvable_of_surjective
    (f := (H.conjugateIso g).hom.onPoints)
    (H.conjugateIso g).toMulEquiv.surjective

/-- Inner conjugation preserves Borel subgroups. -/
public lemma IsBorelSubgroup.conjugate
    {G : Variety k} [AlgebraicGroup G]
    {B : ClosedSubgroup G} (hB : IsBorelSubgroup B)
    (g : Variety.Point G) :
    IsBorelSubgroup (B.conjugate g) := by
  refine ⟨closedSubgroup_conjugate_isConnected B g hB.connected,
    closedSubgroup_conjugate_isSolvable B g hB.solvable, ?_⟩
  intro S hSconnected hSsolvable hBS
  have hBackConnected :=
    closedSubgroup_conjugate_isConnected S g⁻¹ hSconnected
  have hBackSolvable :=
    closedSubgroup_conjugate_isSolvable S g⁻¹ hSsolvable
  have hBackContain : B ≤ S.conjugate g⁻¹ := by
    intro x hx
    apply (S.mem_conjugate_iff g⁻¹ x).mpr
    apply hBS
    apply (B.mem_conjugate_iff g _).mpr
    change x ∈ B.toSubgroup at hx
    simpa [mul_assoc] using hx
  have hBack : S.conjugate g⁻¹ = B :=
    hB.maximal (S.conjugate g⁻¹) hBackConnected hBackSolvable hBackContain
  calc
    S = (S.conjugate g⁻¹).conjugate g := by
      rw [S.conjugate_conjugate]
      simp only [mul_inv_cancel, S.conjugate_one]
    _ = B.conjugate g := by rw [hBack]

section

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_6_2_b
    {G : Variety k} [AlgebraicGroup G] {B₁ B₂ : ClosedSubgroup G}
    (hB₁ : IsBorelSubgroup B₁) (hB₂ : IsBorelSubgroup B₂) :
    ∃ g : Variety.Point G, B₂ = B₁.conjugate g := by sorry

end

end Theory.AlgebraicGroup
