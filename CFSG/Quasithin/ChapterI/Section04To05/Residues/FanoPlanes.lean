module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.StandardMarking
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.PointedCosets
public import Theory.SpecificGroups.PSL3Two.Parabolics.FanoQuotientMark

/-!
# Every original plane residue is the Fano plane

The actual quotient marking identifies the plane group's two parabolics
with the standard PSL₃(2) pair. The coset maps then identify the points and
lines incident with the original plane. If the two quotient parabolics
appear in the opposite order, the explicit Fano duality corrects them.
Translation gives the comparison at every plane of the D-system.

Source: Aschbacher–Smith I.5.4(2), printed p.420. The marking derives from
D2–D3 and preserves the literal ambient point-line incidence.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] {D : Diagram} (S : DSystem D G)

structure FanoPlaneResidue (π : S.Plane) where
  points : Matrix.PSL3Two.Fano.Point ≃ {x : S.Point // S.Inc x π}
  lines : Matrix.PSL3Two.Fano.Line ≃ {l : S.Line // S.Inc l π}
  incident : ∀ p l, S.Inc (points p).val (lines l).val ↔ Matrix.PSL3Two.Fano.Incident p l

theorem exists_baseFanoPlaneResidue : Nonempty (S.FanoPlaneResidue S.basePlane) := by
  obtain ⟨e, he⟩ := S.plane_standard_quotientMark
  let f := S.localQuotientMap 2 e
  have hker := S.localQuotientMap_ker_le 2 e
  have hkP : f.ker ≤ localParabolic S.family 2 0 :=
    hker.trans (S.plane_parabolics.borel_eq ▸ inf_le_left)
  have hkL : f.ker ≤ localParabolic S.family 2 1 :=
    hker.trans (S.plane_parabolics.borel_eq ▸ inf_le_right)
  obtain ⟨m⟩ := Matrix.PSL3Two.Fano.exists_quotientMark
    (localParabolic S.family 2 0) (localParabolic S.family 2 1) f
    (S.localQuotientMap_surjective 2 e) hkP hkL he
  let ep : (S.family 2 ⧸ localParabolic S.family 2 0) ≃
      {x : S.Point // S.Inc x S.basePlane} :=
    (S.pointedCosetEquiv 2 0 (by decide)).trans
      (Equiv.subtypeEquiv (Equiv.refl _) (fun x =>
        ⟨CosetGeometry.Incident.symm S.family, CosetGeometry.Incident.symm S.family⟩))
  let el : (S.family 2 ⧸ localParabolic S.family 2 1) ≃
      {l : S.Line // S.Inc l S.basePlane} :=
    (S.pointedCosetEquiv 2 1 (by decide)).trans
      (Equiv.subtypeEquiv (Equiv.refl _) (fun l =>
        ⟨CosetGeometry.Incident.symm S.family, CosetGeometry.Incident.symm S.family⟩))
  refine ⟨⟨m.points.symm.trans ep, m.lines.symm.trans el, ?_⟩⟩
  intro p l
  change S.Inc (S.pointedCosetEquiv 2 0 _ (m.points.symm p)).val
    (S.pointedCosetEquiv 2 1 _ (m.lines.symm l)).val ↔ _
  rw [← S.pointedCosetEquiv_incident 2 0 1, m.incident,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

namespace FanoPlaneResidue
variable {S} {π : S.Plane} (m : S.FanoPlaneResidue π)

def translate (g : G) : S.FanoPlaneResidue (g • π) where
  points := m.points.trans {
    toFun p := ⟨g • p.val, p.property.smul S g⟩
    invFun p := ⟨g⁻¹ • p.val, by
      simpa only [inv_smul_smul] using p.property.smul S g⁻¹⟩
    left_inv p := Subtype.ext (inv_smul_smul g p.val)
    right_inv p := Subtype.ext (smul_inv_smul g p.val) }
  lines := m.lines.trans {
    toFun l := ⟨g • l.val, l.property.smul S g⟩
    invFun l := ⟨g⁻¹ • l.val, by
      simpa only [inv_smul_smul] using l.property.smul S g⁻¹⟩
    left_inv l := Subtype.ext (inv_smul_smul g l.val)
    right_inv l := Subtype.ext (smul_inv_smul g l.val) }
  incident p l := by
    change S.Inc (g • (m.points p).val) (g • (m.lines l).val) ↔ _
    rw [← m.incident]
    constructor
    · intro h
      simpa only [inv_smul_smul] using h.smul S g⁻¹
    · exact fun h => h.smul S g

include m in
theorem card_points : Nat.card {x : S.Point // S.Inc x π} = 7 := by
  rw [← Nat.card_congr m.points, Nat.card_eq_fintype_card, Matrix.PSL3Two.Fano.card_point]

include m in
theorem card_lines : Nat.card {l : S.Line // S.Inc l π} = 7 := by
  rw [← Nat.card_congr m.lines, Nat.card_eq_fintype_card, Matrix.PSL3Two.Fano.card_line]

end FanoPlaneResidue

theorem exists_fanoPlaneResidue (π : S.Plane) : Nonempty (S.FanoPlaneResidue π) := by
  obtain ⟨m⟩ := S.exists_baseFanoPlaneResidue
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S.basePlane π
  exact ⟨m.translate g⟩

/-- Any two original points in one plane are collinear in the original geometry. -/
theorem collinear_of_common_plane {x y : S.Point} {π : S.Plane}
    (hx : S.Inc x π) (hy : S.Inc y π) : S.Collinear x y := by
  obtain ⟨m⟩ := S.exists_fanoPlaneResidue π
  let p := m.points.symm ⟨x, hx⟩
  let q := m.points.symm ⟨y, hy⟩
  by_cases hpq : p = q
  · have hxy : x = y := by
      have h := congrArg (fun p => (m.points p).val) hpq
      simpa only [p, q, Equiv.apply_symm_apply] using h
    rw [hxy]
    exact S.collinear_refl y
  obtain ⟨l, hl, _⟩ := Matrix.PSL3Two.Fano.unique_line p q hpq
  refine ⟨(m.lines l).val, ?_, ?_⟩
  · have h := (m.incident p l).mpr hl.1
    simpa only [p, Equiv.apply_symm_apply] using h
  · have h := (m.incident q l).mpr hl.2
    simpa only [q, Equiv.apply_symm_apply] using h

/-- The source neighbor core fixes every point of the standard plane. -/
theorem neighborCore_fixes_basePlane_points {g : G} (hg : g ∈ S.neighborCore)
    {y : S.Point} (hy : S.Inc y S.basePlane) : g • y = y := by
  apply S.neighborCore_fixes hg
  apply S.collinear_of_common_plane (π := S.basePlane) _ hy
  exact ⟨1, rfl, rfl⟩

/-- The original plane group acts on its plane points with exactly its two-core as kernel. -/
theorem plane_point_parabolic_normalCore :
    (localParabolic S.family 2 0).normalCore = pCore 2 (S.family 2) := by
  obtain ⟨e, he⟩ := S.plane_standard_quotientMark
  have hk : (S.localQuotientMap 2 e).ker ≤ localParabolic S.family 2 0 :=
    (S.localQuotientMap_ker_le 2 e).trans
      (S.plane_parabolics.borel_eq ▸ inf_le_left)
  have h := Matrix.PSL3Two.Fano.normalCore_eq_ker_of_standard_parabolic
    (localParabolic S.family 2 0) (S.localQuotientMap 2 e)
    (S.localQuotientMap_surjective 2 e) hk (he.imp And.left And.left)
  exact h.trans (S.localQuotientMap_ker 2 e)

/-- I.5.7(5), proved from the original Fano plane rather than assumed in a local-core record. -/
theorem neighborCore_le_planeCore : S.neighborCore ≤ S.Q 2 := by
  intro g hg
  have hg2 : g ∈ S.family 2 :=
    S.T_le 2 (S.Q_le_T 0 (S.neighborCore_le_Q hg))
  let a : S.family 2 := ⟨g, hg2⟩
  have ha : a ∈ pCore 2 (S.family 2) := by
    rw [← S.plane_point_parabolic_normalCore, Subgroup.normalCore_eq_ker]
    apply Equiv.Perm.ext
    intro q
    apply (S.pointedCosetEquiv 2 0 (by decide)).injective
    apply Subtype.ext
    change (S.pointedCosetEquiv 2 0 (by decide) (a • q)).val = _
    rw [S.pointedCosetEquiv_smul]
    exact S.neighborCore_fixes_basePlane_points hg
      (CosetGeometry.Incident.symm S.family
        (S.pointedCosetEquiv 2 0 (by decide) q).property)
  exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩

end Quasithin.I5.DSystem
