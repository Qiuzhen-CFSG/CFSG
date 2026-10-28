module

public import CFSG.Quasithin.ChapterI.Section04To05.C3Recognition.MarkedPlaneAction
public import Theory.LinearAlgebra.BinaryLagrangianKernel

/-!
# The elementary plane core in the original C₃ system

The two-core of the plane vertex fixes its seven incident points. Under the
faithful symplectic marking these span a Lagrangian, so the binary
pointwise-kernel argument makes the core elementary abelian. Index
multiplication through the original point-plane intersection gives 135
planes; the group order and the literal L₃(2) quotient then give core
order 64. Finally both assertions are transported to the original ambient
subgroup, through its actual restriction to the generated group.

These are the elementary and dimension inputs for W=J(T)=O₂(H₀) in
Aschbacher–Smith 13.4.9, printed p.906. They do not assert the remaining
four-orbit classification or ambient fusion.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Matrix Theory.SpecificGroups.SymplecticSix
open Quasithin.I5 Quasithin.I5.C3Recognition
variable {G : Type*} [Group G] {S : DSystem .C3 G}

/-- The actual plane two-core fixes the marked Lagrangian pointwise. -/
theorem marked_plane_core_fixes (m : SymplecticMark S)
    {a : S.family 2} (ha : a ∈ pCore 2 (S.family 2))
    (u : Vector (ZMod 2)) (hu : u ∈ m.planeSpace S.basePlane) :
    toLinear (m.hom a.val) u = u := by
  rcases (m.mem_planeSpace_iff S.basePlane u).mp hu with rfl | ⟨x, hx, rfl⟩
  · exact map_zero _
  have hq : a.val ∈ S.Q 2 := mem_map.mpr ⟨a, ha, rfl⟩
  have hf := S.core_fixes_incident_coset 2 0 (by decide) hq
    (CosetGeometry.Incident.symm S.family hx)
  rw [toLinear_apply, Theory.SpecificGroups.SymplecticSix.smul_eq_mulVec,
    m.equivariant, hf]

/-- Faithfulness of the retained marking makes the plane core elementary. -/
theorem marked_plane_core_elementary (m : SymplecticMark S) :
    IsElementaryAbelian 2 (pCore 2 (S.family 2)) := by
  let ρ : pCore 2 (S.family 2) →*
      (Vector (ZMod 2) ≃ₗ[ZMod 2] Vector (ZMod 2)) :=
    toLinear.comp ((m.hom.comp (S.family 2).subtype).comp (pCore 2 (S.family 2)).subtype)
  apply Theory.LinearAlgebra.binary_lagrangian_kernel_isElementaryAbelian
    (form (ZMod 2)) (m.planeSpace S.basePlane) (m.planeSpace_orthogonal _) ρ
  · intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply m.hom_injective
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    have he := congrArg (fun f : Vector (ZMod 2) ≃ₗ[ZMod 2] Vector (ZMod 2) =>
      f (Pi.single j 1) i) hab
    change (m.hom a.val.val).val.mulVec (Pi.single j 1) i =
      (m.hom b.val.val).val.mulVec (Pi.single j 1) i at he
    simpa [Matrix.mulVec_single] using he
  · intro a x y
    exact preserves_form (m.hom a.val.val) x y
  · intro a w hw
    exact marked_plane_core_fixes m a.property w hw

/-- Elementary-abelianity follows from the original D-system alone. -/
theorem plane_core_elementary (S : DSystem .C3 G) :
    IsElementaryAbelian 2 (pCore 2 (S.family 2)) := by
  let d := S.source_local_polar_facts
  obtain ⟨m⟩ := exists_symplecticMark S
    ⟨S.c3_points_card d, S.faithful_points, S.c3_exists_noncollinear,
      fun x y h => S.source_one_or_all_triples d x y h⟩
  exact marked_plane_core_elementary m

/-- Transport to the original ambient subgroup using the literal third vertex. -/
theorem original_plane_core_elementary (E H : Subgroup G) (hHE : H ≤ E)
    (S : DSystem .C3 E) (hthird : S.family 2 = H.subgroupOf E) :
    IsElementaryAbelian 2 (H.pCoreIn 2) := by
  let e : S.family 2 ≃* H :=
    (MulEquiv.subgroupCongr hthird).trans (subgroupOfEquivOfLe hHE)
  let := plane_core_elementary S
  have h : IsElementaryAbelian 2 ((pCore 2 (S.family 2)).map e.toMonoidHom) :=
    IsElementaryAbelian.map e.toMonoidHom
  rw [pCore_map_iso] at h
  let := h
  exact IsElementaryAbelian.map H.subtype


/-- The plane vertex has index 135, from the original local incidence counts. -/
theorem c3_plane_index (S : DSystem .C3 G) : (S.family 2).index = 135 := by
  have hpoint : (S.family 0).index = 63 :=
    S.c3_points_card S.source_local_polar_facts
  have h15 : (S.family 2).relIndex (S.family 0) = 15 :=
    S.c3_point_parabolic_indices.2
  have h7 : (S.family 0).relIndex (S.family 2) = 7 := by
    obtain ⟨r⟩ := S.exists_fanoPlaneResidue S.basePlane
    let e : {x : S.Point // S.Inc x S.basePlane} ≃
        {x : S.Point // S.Inc S.basePlane x} :=
      Equiv.subtypeEquiv (Equiv.refl _) (fun x =>
        ⟨CosetGeometry.Incident.symm S.family, CosetGeometry.Incident.symm S.family⟩)
    have hh := r.card_points
    rw [Nat.card_congr e, S.incidentFiber_card 2 0 (by decide) S.basePlane] at hh
    exact hh
  have hleft := relIndex_mul_index
    (show S.family 0 ⊓ S.family 2 ≤ S.family 0 from inf_le_left)
  have hright := relIndex_mul_index
    (show S.family 0 ⊓ S.family 2 ≤ S.family 2 from inf_le_right)
  rw [inf_relIndex_left, h15, hpoint] at hleft
  rw [inf_relIndex_right, h7] at hright
  omega

/-- The elementary plane core has order 64. -/
theorem plane_core_card (S : DSystem .C3 G) :
    Nat.card (pCore 2 (S.family 2)) = 64 := by
  obtain ⟨e⟩ := S.plane_quotient
  have hquot : Nat.card (S.family 2 ⧸ pCore 2 (S.family 2)) = 168 := by
    rw [Nat.card_congr (e.trans Matrix.PSL3Two.equiv.symm).toEquiv]
    exact Matrix.PSL3Two.card_SL
  have hcore := (pCore 2 (S.family 2)).card_mul_index
  change Nat.card (pCore 2 (S.family 2)) *
    Nat.card (S.family 2 ⧸ pCore 2 (S.family 2)) = Nat.card (S.family 2) at hcore
  rw [hquot] at hcore
  have hglobal := (S.family 2).card_mul_index
  rw [c3_plane_index, C3Recognition.card_eq S] at hglobal
  omega

/-- The order calculation uses the same ambient core as the fusion argument. -/
theorem original_plane_core_card (E H : Subgroup G) (hHE : H ≤ E)
    (S : DSystem .C3 E) (hthird : S.family 2 = H.subgroupOf E) :
    Nat.card (H.pCoreIn 2) = 64 := by
  let e : S.family 2 ≃* H :=
    (MulEquiv.subgroupCongr hthird).trans (subgroupOfEquivOfLe hHE)
  have hc : Nat.card (pCore 2 H) = 64 := by
    rw [← pCore_map_iso 2 e, card_map_of_injective e.injective]
    exact plane_core_card S
  simpa only [pCoreIn, card_map_of_injective H.subtype_injective] using hc

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
