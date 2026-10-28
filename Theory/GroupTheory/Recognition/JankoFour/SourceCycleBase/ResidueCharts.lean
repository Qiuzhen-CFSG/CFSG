module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Geometry
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.Residue
/-!
# Symplectic charts on the literal point-plane flags

Translate both incidence charts by the same representative of the point.
Equivariance under the original Todd projection makes the transported δ₁
label exactly shared-octad incidence. Restricting to a plane and applying
the native sextet equivalence gives the correct dual binary symplectic chart.
No new geometry premise is introduced.

Source: Aschbacher–Segev (1991), opening of §7 and (7.3), p.603.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open GraphUniquenessSystem
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {P : LocalGeometry.LocalSubgroups.PointData z} {L : LocalGeometry.LocalSubgroups.LineData z P}
namespace ResidueChart
variable (c : ResidueChart P L)

theorem representative_inv_point (x : Point P) : (representative x)⁻¹ • x = Cosets.vertex P.M 1 := by
  calc
    _ = (representative x)⁻¹ • Cosets.vertex P.M (representative x) :=
      congrArg ((representative x)⁻¹ • ·) (vertex_representative x).symm
    _ = _ := by rw [Cosets.smul_vertex, inv_mul_cancel]

noncomputable def linesAt (x : Point P) : {l : Line L // OnLine L x l} ≃ Native.Line :=
  (show {l : Line L // OnLine L x l} ≃ {l : Line L // OnLine L (Cosets.vertex P.M 1) l} from
    { toFun := fun l => ⟨(representative x)⁻¹ • l.val, by
        simpa only [OnLine, OnPlane, representative_inv_point x] using incident_smul (representative x)⁻¹ l.property⟩
      invFun := fun l => ⟨representative x • l.val, by
        have hp : representative x • Cosets.vertex P.M 1 = x := by
          rw [Cosets.smul_vertex, mul_one, vertex_representative]
        simpa only [OnLine, OnPlane, hp] using incident_smul (representative x) l.property⟩
      left_inv := fun l => Subtype.ext (smul_inv_smul _ _)
      right_inv := fun l => Subtype.ext (inv_smul_smul _ _) }).trans c.lines

noncomputable def planesAt (x : Point P) : {π : Plane z // OnPlane P x π} ≃ Native.Plane :=
  (show {π : Plane z // OnPlane P x π} ≃ {π : Plane z // OnPlane P (Cosets.vertex P.M 1) π} from
    { toFun := fun π => ⟨(representative x)⁻¹ • π.val, by
        simpa only [OnLine, OnPlane, representative_inv_point x] using incident_smul (representative x)⁻¹ π.property⟩
      invFun := fun π => ⟨representative x • π.val, by
        have hp : representative x • Cosets.vertex P.M 1 = x := by
          rw [Cosets.smul_vertex, mul_one, vertex_representative]
        simpa only [OnLine, OnPlane, hp] using incident_smul (representative x) π.property⟩
      left_inv := fun π => Subtype.ext (smul_inv_smul _ _)
      right_inv := fun π => Subtype.ext (inv_smul_smul _ _) }).trans c.planes

theorem incidenceAt (x : Point P) (l : {l : Line L // OnLine L x l})
    (π : {π : Plane z // OnPlane P x π}) :
    LineOnPlane L l.val π.val ↔ Native.Incident (c.linesAt x l) (c.planesAt x π) := by
  change _ ↔ Native.Incident (c.lines _) (c.planes _)
  rw [← c.incidence]
  exact (incident_smul_iff l.val π.val (representative x)⁻¹).symm

theorem lineType_one_base (a b : {l : Line L // OnLine L (Cosets.vertex P.M 1) l}) :
    LineType c 1 (Cosets.vertex P.M 1) a.val b.val ↔ Native.Delta 1 (c.lines a) (c.lines b) := by
  constructor
  · rintro ⟨g,a',b',hg,ha,hb,hd⟩
    have hgM := (Cosets.vertex_eq_base P.M g).mp hg
    have hea := c.lines_equivariant ⟨g,hgM⟩ a' a ha
    have heb := c.lines_equivariant ⟨g,hgM⟩ b' b hb
    change (c.lines a).parts ≠ (c.lines b).parts ∧ ((c.lines a).parts ∩ (c.lines b).parts).Nonempty
    rw [hea,heb,← Finset.smul_finset_inter]
    refine ⟨(MulAction.injective (P.projection ⟨g,hgM⟩)).ne hd.1, ?_⟩
    obtain ⟨A,hA⟩ := hd.2
    exact ⟨P.projection ⟨g,hgM⟩ • A, Finset.smul_mem_smul_finset hA⟩
  · intro hd
    exact ⟨1,a,b, rfl, one_smul _ _, one_smul _ _,hd⟩

theorem lineType_one_at (x : Point P) (a b : {l : Line L // OnLine L x l}) :
    LineType c 1 x a.val b.val ↔ Native.Delta 1 (c.linesAt x a) (c.linesAt x b) := by
  change _ ↔ Native.Delta 1 (c.lines _) (c.lines _)
  rw [← c.lineType_one_base]
  change LineType c 1 x a.val b.val ↔
    LineType c 1 (Cosets.vertex P.M 1) ((representative x)⁻¹ • a.val) ((representative x)⁻¹ • b.val)
  rw [← representative_inv_point x]
  exact (lineType_smul_iff c 1 x a.val b.val (representative x)⁻¹).symm

/-- Lines in the literal point-plane flag, mapped to native incident trios. -/
noncomputable def flagLinesNative (x : Point P) (π : Plane z) (hxπ : OnPlane P x π) :
    {l : Line L // OnLine L x l ∧ LineOnPlane L l π} ≃
      {l : Native.Line // Native.Incident l (c.planesAt x ⟨π,hxπ⟩)} where
  toFun l := ⟨c.linesAt x ⟨l.val,l.property.1⟩,
    (c.incidenceAt x ⟨l.val,l.property.1⟩ ⟨π,hxπ⟩).mp l.property.2⟩
  invFun l := ⟨((c.linesAt x).symm l.val).val, ((c.linesAt x).symm l.val).property,
    (c.incidenceAt x ((c.linesAt x).symm l.val) ⟨π,hxπ⟩).mpr (by simpa using l.property)⟩
  left_inv l := by
    apply Subtype.ext
    change ((c.linesAt x).symm ((c.linesAt x) ⟨l.val,l.property.1⟩)).val = l.val
    exact congrArg Subtype.val ((c.linesAt x).symm_apply_apply _)
  right_inv l := Subtype.ext ((c.linesAt x).apply_symm_apply _)

noncomputable def tetradLabel (π : Native.Plane) : Fin 6 ≃ {A // A ∈ π.parts} :=
  (Fintype.equivFinOfCardEq (by simpa using π.card)).symm

/-- The point-plane residue with the correct dual symplectic orientation. -/
noncomputable def flagLines (x : Point P) (π : Plane z) (hxπ : OnPlane P x π) :
    {l : Line L // OnLine L x l ∧ LineOnPlane L l π} ≃
      Theory.SpecificGroups.SymmetricSix.Syntheme :=
  (c.flagLinesNative x π hxπ).trans
    (Native.residueEquiv _ (tetradLabel (c.planesAt x ⟨π,hxπ⟩)))

theorem flagLines_collinear_iff (x : Point P) (π : Plane z) (hxπ : OnPlane P x π)
    (l m : {l : Line L // OnLine L x l ∧ LineOnPlane L l π}) :
    Theory.SpecificGroups.SymmetricSix.synthemeCollinear
      (c.flagLines x π hxπ l) (c.flagLines x π hxπ m) ↔ LineType c 1 x l.val m.val := by
  change Theory.SpecificGroups.SymmetricSix.synthemeCollinear
    (Native.residueEquiv _ _ _) (Native.residueEquiv _ _ _) ↔ _
  rw [← Native.residueEquiv_delta_one]
  change Native.Delta 1 (c.linesAt x ⟨l.val,l.property.1⟩)
    (c.linesAt x ⟨m.val,m.property.1⟩) ↔ _
  exact (c.lineType_one_at x ⟨l.val,l.property.1⟩ ⟨m.val,m.property.1⟩).symm

end ResidueChart
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
