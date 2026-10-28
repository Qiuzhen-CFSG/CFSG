module

public import Theory.AlgebraicGroup.Solvable.SubtorusCentralizer
public import Theory.AlgebraicGroup.Borel.Defs
public import Theory.AlgebraicGroup.ClosedSubgroup.Connected

/-!
# Local centralizers inside common Borel subgroups

A torus `S` and a point `a` centralizing it, when contained in a common Borel
`B`, lie in the connected solvable centralizer `C_B(S)`. We construct the
actual torus inside `B`, and map its centralizer back to `G`. Its connected
image is contained in `C_G(S)`, so `a` lies in `C_G(S)^0`.

Consequently, common Borel containment for every centralizing point implies
`C_G(S) = C_G(S)^0`. This is the final connectedness argument of Borel,
*Linear Algebraic Groups*, §11.12 (`refs/KGroup/Bor1/Chapter4.tex`). The
common Borel is supplied by the complete fixed-locus argument in the sibling
`CommonBorel` module; its earlier element-coverage premise remains explicit.
-/

open Theory.AlgebraicGroup
universe u
namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.CartanGeometry
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
set_option linter.style.haveILetI false

omit [IsAlgClosed k] in
private theorem carrier_connected (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ H} := Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

/-- Inside a common Borel, the connected solvable centralizer of `S` contains
`a`; its actual inclusion into `G` places `a` in the full centralizer's identity
component. -/
public theorem mem_centralizer_identityComponent_of_common_borel
    {S B : ClosedSubgroup G} (hS : IsSubtorus S) (hB : IsBorelSubgroup B)
    (hSB : S ≤ B) {a : Variety.Point G} (haB : a ∈ B)
    (ha : a ∈ S.centralizer) : a ∈ S.centralizer.identityComponentAmbient := by
  let j : AlgebraicGroup.Morphism S.carrierVariety B.carrierVariety :=
    S.inclusion.codRestrictClosedSubgroup B (fun s => hSB (S.pointEquiv s).property)
  have hj (s : Variety.Point S.carrierVariety) :
      B.inclusion.onPoints (j.onPoints s) = S.inclusion.onPoints s :=
    S.inclusion.codRestrictClosedSubgroup_inclusion_apply B _ s
  let SB := j.imageClosedSubgroup
  have hSBtorus : IsSubtorus SB := morphism_image_isTorus j hS
  let C := SB.centralizer
  letI : AlgebraicGroup C.carrierVariety := C.carrierAlgebraicGroup
  have hCconn : Variety.IsConnected C.carrierVariety :=
    subtorus_centralizer_isConnected_of_isConnected_of_isSolvable
      (carrier_connected B hB.connected) hB.solvable hSBtorus
  let f := B.inclusion.comp C.inclusion
  have himageconn := f.imageClosedSubgroup_isConnected hCconn
  have himagele : f.imageClosedSubgroup ≤ S.centralizer := by
    intro x hx
    change ∃ y, f.onPoints y = x at hx
    obtain ⟨y, rfl⟩ := hx
    change f.onPoints y ∈ Subgroup.centralizer (S.toSubgroup : Set (Variety.Point G))
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    let sS : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨s, hs⟩
    have hsval : S.inclusion.onPoints sS = s := by
      change (S.pointEquiv sS).val = s
      simp [sS]
    have hjmem : j.onPoints sS ∈ SB := ⟨sS, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp (C.pointEquiv y).property
      (j.onPoints sS) hjmem
    have hamb := congrArg B.inclusion.onPoints hcomm
    change s * B.inclusion.onPoints (C.pointEquiv y).val =
      B.inclusion.onPoints (C.pointEquiv y).val * s
    simpa only [map_mul, hj, hsval] using hamb
  have hle := connected_closedSubgroup_le_identityComponentAmbient
    f.imageClosedSubgroup S.centralizer himageconn himagele
  apply hle
  let aB : Variety.Point B.carrierVariety := B.pointEquiv.symm ⟨a, haB⟩
  have haBval : B.inclusion.onPoints aB = a := by
    change (B.pointEquiv aB).val = a
    simp [aB]
  have haC : aB ∈ C := by
    change aB ∈ Subgroup.centralizer (SB.toSubgroup : Set (Variety.Point B.carrierVariety))
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨t, rfl⟩ := hs
    apply B.inclusion_injective
    simp only [map_mul, haBval, hj]
    exact Subgroup.mem_centralizer_iff.mp ha _ (S.pointEquiv t).property
  let aC : Variety.Point C.carrierVariety := C.pointEquiv.symm ⟨aB, haC⟩
  change ∃ y, f.onPoints y = a
  refine ⟨aC, ?_⟩
  change B.inclusion.onPoints (C.pointEquiv aC).val = a
  simp only [aC, Equiv.apply_symm_apply, haBval]

/-- If each point centralizing a torus lies in a Borel containing that torus,
then its full centralizer equals its identity component. -/
public theorem centralizer_identityComponent_eq_of_common_borels
    {S : ClosedSubgroup G} (hS : IsSubtorus S)
    (hcommon : ∀ a : Variety.Point G, a ∈ S.centralizer →
      ∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧ S ≤ B ∧ a ∈ B) :
    S.centralizer.identityComponentAmbient = S.centralizer := by
  apply SetLike.coe_injective
  apply Set.Subset.antisymm S.centralizer.identityComponentAmbient_le
  intro a ha
  obtain ⟨B, hB, hSB, haB⟩ := hcommon a ha
  exact mem_centralizer_identityComponent_of_common_borel hS hB hSB haB ha

/-- The local Borel centralizers prove connectedness of the entire centralizer,
provided every centralizing point has a common Borel with the torus. -/
public theorem centralizer_isConnected_of_common_borels
    {S : ClosedSubgroup G} (hS : IsSubtorus S)
    (hcommon : ∀ a : Variety.Point G, a ∈ S.centralizer →
      ∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧ S ≤ B ∧ a ∈ B) :
    Variety.IsConnected S.centralizer.carrierVariety := by
  apply carrier_connected
  rw [← centralizer_identityComponent_eq_of_common_borels hS hcommon]
  exact S.centralizer.identityComponentAmbient_isConnected

end Theory.AlgebraicGroup.SemisimpleCenterContainment.CartanGeometry
