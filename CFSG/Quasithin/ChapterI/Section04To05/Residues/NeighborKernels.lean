module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.CoreActions
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.FanoPlanes

/-!
# Original point-core kernels on a line

The point core already fixes every plane through the base line, by the
string containment. Its kernel on that line's three points is therefore
exactly Q₀∩Q₁, using the full line-residue kernel. If Q₀ is contained in
Q₁, conjugation within the point group makes it fix every neighboring point;
then the Fano-plane calculation places it in Q₂.

Source: I.5.7(1,5–6), printed pp.420–421.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] {D : Diagram} (S : DSystem D G)

theorem point_core_fixes_baseLine_planes {g : G} (hg : g ∈ S.Q 0)
    {π : S.Plane} (hπ : S.Inc S.baseLine π) : g • π = π := by
  apply S.core_fixes_incident_coset 0 2 (by decide) hg
  exact S.point_line_plane (show S.Inc S.basePoint S.baseLine from ⟨1, rfl, rfl⟩) hπ

theorem point_core_line_kernel :
    S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Inc y S.baseLine} = S.Q 0 ⊓ S.Q 1 := by
  apply le_antisymm
  · intro g hg
    refine ⟨hg.1, ?_⟩
    have hg1 : g ∈ S.family 1 := S.T_le 1 (S.Q_le_T 0 hg.1)
    let a : S.family 1 := ⟨g, hg1⟩
    have ha : a ∈ pCore 2 (S.family 1) := by
      rw [← S.residue_kernel 1]
      apply Equiv.Perm.ext
      rintro ⟨⟨i, v⟩, hi, hv⟩
      apply Subtype.ext
      fin_cases i
      · change (⟨0, g • v⟩ : S.Vertex) = ⟨0, v⟩
        rw [(mem_fixingSubgroup_iff G).mp hg.2 v (CosetGeometry.Incident.symm S.family hv)]
      · exact (hi rfl).elim
      · change (⟨2, g • v⟩ : S.Vertex) = ⟨2, v⟩
        rw [S.point_core_fixes_baseLine_planes hg.1 hv]
    exact mem_map.mpr ⟨a, ha, rfl⟩
  · intro g hg
    refine ⟨hg.1, (mem_fixingSubgroup_iff G).mpr ?_⟩
    intro y hy
    exact S.core_fixes_incident_coset 1 0 (by decide) hg.2
      (CosetGeometry.Incident.symm S.family hy)

theorem point_core_eq_neighborCore_of_le_lineCore (h : S.Q 0 ≤ S.Q 1) :
    S.Q 0 = S.neighborCore := by
  apply le_antisymm _ S.neighborCore_le_Q
  intro g hg
  refine ⟨hg, (mem_fixingSubgroup_iff G).mpr ?_⟩
  rintro y ⟨l, hxl, hyl⟩
  obtain ⟨a, ha, hal⟩ := (CosetGeometry.incident_base_iff S.family 0 ⟨1, l⟩).mp hxl
  have hl : a • S.baseLine = l := by
    change ((a * 1 : G) : G ⧸ S.family 1) = l
    simpa only [mul_one] using hal
  have hn := S.family_le_normalizer_Q 0 ((S.family 0).inv_mem ha)
  have hconj : a⁻¹ * g * a ∈ S.Q 0 := by
    simpa only [inv_inv] using (mem_normalizer_iff.mp hn g).mp hg
  have hy' : S.Inc (a⁻¹ • y) S.baseLine := by
    simpa only [← hl, inv_smul_smul] using hyl.smul S a⁻¹
  have hf := S.core_fixes_incident_coset 1 0 (by decide) (h hconj)
    (CosetGeometry.Incident.symm S.family hy')
  have hh := congrArg (a • ·) hf
  simpa only [mul_smul, smul_inv_smul, inv_smul_smul] using hh

theorem point_core_le_planeCore_of_le_lineCore (h : S.Q 0 ≤ S.Q 1) : S.Q 0 ≤ S.Q 2 := by
  rw [S.point_core_eq_neighborCore_of_le_lineCore h]
  exact S.neighborCore_le_planeCore

theorem le_neighborCore_of_normalized_line_kernel (N : Subgroup G)
    (hN : N ≤ S.Q 0) (hn : S.family 0 ≤ normalizer (N : Set G))
    (hfix : N ≤ fixingSubgroup G {y : S.Point | S.Inc y S.baseLine}) :
    N ≤ S.neighborCore := by
  intro g hg
  refine ⟨hN hg, (mem_fixingSubgroup_iff G).mpr ?_⟩
  rintro y ⟨l, hxl, hyl⟩
  obtain ⟨a, ha, hal⟩ := (CosetGeometry.incident_base_iff S.family 0 ⟨1, l⟩).mp hxl
  have hl : a • S.baseLine = l := by
    change ((a * 1 : G) : G ⧸ S.family 1) = l
    simpa only [mul_one] using hal
  have hconj : a⁻¹ * g * a ∈ N := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp (hn ((S.family 0).inv_mem ha)) g).mp hg
  have hy' : S.Inc (a⁻¹ • y) S.baseLine := by
    simpa only [← hl, inv_smul_smul] using hyl.smul S a⁻¹
  have hf := (mem_fixingSubgroup_iff G).mp (hfix hconj) _ hy'
  have hh := congrArg (a • ·) hf
  simpa only [mul_smul, smul_inv_smul, inv_smul_smul] using hh

end Quasithin.I5.DSystem
