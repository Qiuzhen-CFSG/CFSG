module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.DistanceTwoStart
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.TranslatedCoreActions

/-!
# Original noncoplanar two-line paths

The paths retain their original middle and end points and both lines.
The local polar stabilizer transporter, supplied by the literal point
residue comparison, combines with the proved point-core adjustments to
make these paths a single orbit under the initial point stabilizer.

This is the group-action step of I.5.9(3i), pp.421–422. The explicit local
transporter is the independent I.5.4 polar-residue conclusion; no global
orbit or recognition conclusion is assumed.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem coplanarLines_refl (l : S.Line) : S.CoplanarLines l l := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective l
  exact ⟨(g : G ⧸ S.family 2), ⟨g, rfl, rfl⟩, ⟨g, rfl, rfl⟩⟩

theorem coplanarLines_smul_iff (g : G) (l m : S.Line) :
    S.CoplanarLines (g • l) (g • m) ↔ S.CoplanarLines l m := by
  constructor
  · rintro ⟨π, hl, hm⟩
    exact ⟨g⁻¹ • π, by simpa only [inv_smul_smul] using hl.smul S g⁻¹,
      by simpa only [inv_smul_smul] using hm.smul S g⁻¹⟩
  · rintro ⟨π, hl, hm⟩
    exact ⟨g • π, hl.smul S g, hm.smul S g⟩

structure TwoLinePath (x : S.Point) where
  middle : S.Point
  endpoint : S.Point
  first : S.Line
  second : S.Line
  left_ne : x ≠ middle
  right_ne : middle ≠ endpoint
  left_inc : S.Inc x first
  middle_first : S.Inc middle first
  middle_second : S.Inc middle second
  right_inc : S.Inc endpoint second
  noncoplanar : ¬ S.CoplanarLines first second

namespace TwoLinePath
variable {S} {x : S.Point} (p : S.TwoLinePath x)

theorem lines_ne : p.first ≠ p.second := fun h =>
  p.noncoplanar (h ▸ S.coplanarLines_refl p.first)

def translate (g : G) : S.TwoLinePath (g • x) where
  middle := g • p.middle
  endpoint := g • p.endpoint
  first := g • p.first
  second := g • p.second
  left_ne := (MulAction.injective g).ne p.left_ne
  right_ne := (MulAction.injective g).ne p.right_ne
  left_inc := p.left_inc.smul S g
  middle_first := p.middle_first.smul S g
  middle_second := p.middle_second.smul S g
  right_inc := p.right_inc.smul S g
  noncoplanar := fun h => p.noncoplanar ((S.coplanarLines_smul_iff g _ _).mp h)

end TwoLinePath

theorem exists_twoLinePath (x : S.Point) : Nonempty (S.TwoLinePath x) := by
  obtain ⟨y, z, l, m, hxy, hyz, hxl, hyl, hym, hzm, _, hplane⟩ :=
    S.exists_noncoplanar_two_line_path x
  exact ⟨⟨y, z, l, m, hxy, hyz, hxl, hyl, hym, hzm, hplane⟩⟩

theorem point_neighbor_transporter {x y z : S.Point}
    (hy : S.Collinear x y) (hz : S.Collinear x z) (hxy : x ≠ y) (hxz : x ≠ z) :
    ∃ g : G, g • x = x ∧ g • y = z := by
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq G S.basePoint x
  have hy' : S.Collinear S.basePoint (b⁻¹ • y) := by
    simpa only [← hb, inv_smul_smul] using hy.smul S b⁻¹
  have hz' : S.Collinear S.basePoint (b⁻¹ • z) := by
    simpa only [← hb, inv_smul_smul] using hz.smul S b⁻¹
  obtain ⟨a, ha, he⟩ := S.base_neighbors_transitive hy' hz'
    (fun h => hxy (by simpa only [hb, smul_inv_smul] using congrArg (b • ·) h))
    (fun h => hxz (by simpa only [hb, smul_inv_smul] using congrArg (b • ·) h))
  have hax : a • S.basePoint = S.basePoint := by
    apply MulAction.mem_stabilizer_iff.mp
    rwa [S.stabilizer_basePoint]
  exact ⟨b * a * b⁻¹, by rw [← hb, mul_smul, mul_smul, inv_smul_smul, hax],
    by simpa only [mul_smul, smul_inv_smul] using congrArg (b • ·) he⟩

theorem twoLinePaths_transitive
    (hlocal : ∀ (x : S.Point) (l k m : S.Line), S.Inc x l → S.Inc x k → S.Inc x m →
      ¬ S.CoplanarLines l k → ¬ S.CoplanarLines l m →
      ∃ g : G, g • x = x ∧ g • l = l ∧ g • k = m)
    {x : S.Point} (p q : S.TwoLinePath x) :
    ∃ g : G, g • x = x ∧ g • p.middle = q.middle ∧ g • p.endpoint = q.endpoint ∧
      g • p.first = q.first ∧ g • p.second = q.second := by
  obtain ⟨a, hax, hay⟩ := S.point_neighbor_transporter
    ⟨p.first, p.left_inc, p.middle_first⟩ ⟨q.first, q.left_inc, q.middle_first⟩ p.left_ne q.left_ne
  have haf : a • p.first = q.first := by
    apply S.unique_line q.left_ne
    · simpa only [hax] using p.left_inc.smul S a
    · simpa only [hay] using p.middle_first.smul S a
    · exact q.left_inc
    · exact q.middle_first
  have haps : S.Inc q.middle (a • p.second) := by simpa only [hay] using p.middle_second.smul S a
  have hnc : ¬ S.CoplanarLines q.first (a • p.second) := by
    rw [← haf, S.coplanarLines_smul_iff]
    exact p.noncoplanar
  obtain ⟨b, hby, hbf, hbs⟩ := hlocal q.middle q.first (a • p.second) q.second
    q.middle_first haps q.middle_second hnc q.noncoplanar
  obtain ⟨c, hcy, hcx, hcl⟩ := S.exists_point_pair_fixer_same_lines
    q.middle_first q.left_inc q.left_ne.symm hby hbf
  have hcf : c • q.first = q.first := (hcl q.first q.middle_first).trans hbf
  have hcs : c • (a • p.second) = q.second := (hcl _ haps).trans hbs
  have hcam : (c * a) • p.middle = q.middle := by rw [mul_smul, hay, hcy]
  have hcae : S.Inc ((c * a) • p.endpoint) q.second := by
    simpa only [mul_smul, hcs] using p.right_inc.smul S (c * a)
  have hne : q.middle ≠ (c * a) • p.endpoint := fun h =>
    p.right_ne ((MulAction.injective (c * a)) (hcam.trans h))
  obtain ⟨d, hdf, hdl, hde⟩ := S.exists_line_pointwise_fixer_transporter
    q.middle_first q.middle_second q.lines_ne hcae q.right_inc hne q.right_ne
  refine ⟨d * (c * a), ?_, ?_, ?_, ?_, ?_⟩
  · rw [mul_smul, mul_smul, hax, hcx, hdf x q.left_inc]
  · rw [mul_smul, hcam, hdf q.middle q.middle_first]
  · simpa only [mul_smul] using hde
  · rw [mul_smul, mul_smul, haf, hcf, hdl q.first q.middle_first]
  · rw [mul_smul, mul_smul, hcs, hdl q.second q.middle_second]

end Quasithin.I5.DSystem
