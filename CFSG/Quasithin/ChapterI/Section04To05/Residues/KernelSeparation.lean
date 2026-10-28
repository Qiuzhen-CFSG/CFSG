module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.KernelNonNormal
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.PointFaithfulness
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

/-!
# Unique original lines and faithful original points

Conjugation transports the point-core kernels on incident lines. The
point-line parabolic is maximal in the point group, so two equal kernels
would make the base kernel point-group invariant. The local core argument
excludes this. The previously proved three-point argument then gives unique
lines, and D4 gives faithfulness on the original point coset space.

Source: I.5.7(6)–I.5.8, printed p.421. All premises of the earlier
unique-line and faithfulness reductions are discharged from D1–D5 here.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem point_line_kernel_conjugate (l : S.Line) {a : G} (ha : a ∈ S.family 0) :
    (S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Inc y l}).map (MulAut.conj a).toMonoidHom =
      S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Inc y (a • l)} := by
  have hset : a • {y : S.Point | S.Inc y l} = {y : S.Point | S.Inc y (a • l)} := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change S.Inc (a⁻¹ • y) l ↔ S.Inc y (a • l)
    constructor
    · intro h
      simpa only [smul_inv_smul] using h.smul S a
    · intro h
      simpa only [inv_smul_smul] using h.smul S a⁻¹
  have hq : (S.Q 0).map (MulAut.conj a).toMonoidHom = S.Q 0 :=
    mem_normalizer_iff_map_conj_eq.mp (S.family_le_normalizer_Q 0 ha)
  rw [Subgroup.map_inf _ _ _ (MulAut.conj a).injective, hq,
    SubMulAction.fixingSubgroup_map_conj_eq hset]

theorem pair_normalizes_point_line_kernel :
    S.pair 0 1 ≤ normalizer (S.Q 0 ⊓ S.Q 1 : Subgroup G) :=
  (le_inf (inf_le_left.trans (S.family_le_normalizer_Q 0))
    (inf_le_right.trans (S.family_le_normalizer_Q 1))).trans
      inf_normalizer_le_normalizer_inf

theorem base_line_eq_of_point_kernel_eq {l : S.Line} (hl : S.Inc S.basePoint l)
    (he : S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Inc y S.baseLine} =
      S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Inc y l}) : S.baseLine = l := by
  obtain ⟨a, ha, hal⟩ := (CosetGeometry.incident_base_iff S.family 0 ⟨1, l⟩).mp hl
  have hline : a • S.baseLine = l := by
    change ((a * 1 : G) : G ⧸ S.family 1) = l
    simpa only [mul_one] using hal
  have hc := S.point_line_kernel_conjugate S.baseLine ha
  rw [hline, ← he, S.point_core_line_kernel] at hc
  have han : a ∈ normalizer (S.Q 0 ⊓ S.Q 1 : Subgroup G) :=
    mem_normalizer_iff_map_conj_eq.mpr hc
  let N := (normalizer (S.Q 0 ⊓ S.Q 1 : Subgroup G)).subgroupOf (S.family 0)
  have hPN : localParabolic S.family 0 1 ≤ N := by
    intro b hb
    exact S.pair_normalizes_point_line_kernel ⟨b.property, hb⟩
  rcases S.point_parabolics.left_maximal.le_iff.mp hPN with htop | hpar
  · have hn : S.family 0 ≤ normalizer (S.Q 0 ⊓ S.Q 1 : Subgroup G) := by
      intro b hb
      exact (show (⟨b, hb⟩ : S.family 0) ∈ N from htop ▸ mem_top _)
    exact (S.point_line_kernel_not_normalized hn).elim
  · have haP : (⟨a, ha⟩ : S.family 0) ∈ localParabolic S.family 0 1 := hpar ▸ han
    have hfix : a • S.baseLine = S.baseLine := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [S.stabilizer_baseLine]
      exact haP
    exact hfix.symm.trans hline

/-- The exact missing premise of the original unique-line reduction. -/
theorem point_line_kernel_separation (l m : S.Line)
    (hl : S.Inc S.basePoint l) (hm : S.Inc S.basePoint m)
    (he : S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Inc y l} =
      S.Q 0 ⊓ fixingSubgroup G {y : S.Point | S.Inc y m}) : l = m := by
  obtain ⟨a, ha, hal⟩ := (CosetGeometry.incident_base_iff S.family 0 ⟨1, l⟩).mp hl
  have hline : a • S.baseLine = l := by
    change ((a * 1 : G) : G ⧸ S.family 1) = l
    simpa only [mul_one] using hal
  have ha' := (S.family 0).inv_mem ha
  have hp : a⁻¹ • S.basePoint = S.basePoint := by
    apply MulAction.mem_stabilizer_iff.mp
    rwa [S.stabilizer_basePoint]
  have hm' : S.Inc S.basePoint (a⁻¹ • m) := by
    simpa only [hp] using hm.smul S a⁻¹
  have he' := congrArg (Subgroup.map (MulAut.conj a⁻¹).toMonoidHom) he
  rw [S.point_line_kernel_conjugate l ha', S.point_line_kernel_conjugate m ha',
    ← hline, inv_smul_smul] at he'
  have hh := S.base_line_eq_of_point_kernel_eq hm' he'
  have h := congrArg (a • ·) hh
  simpa only [hline, smul_inv_smul] using h

/-- I.5.8(1), for the original C₃ coset geometry and no further premise. -/
theorem unique_line {x y : S.Point} (hxy : x ≠ y) {l m : S.Line}
    (hxl : S.Inc x l) (hyl : S.Inc y l) (hxm : S.Inc x m) (hym : S.Inc y m) : l = m :=
  S.unique_line_of_kernel_separation S.point_line_kernel_separation hxy hxl hyl hxm hym

/-- I.5.8(2), for the original point action. -/
theorem faithful_points : FaithfulSMul G S.Point :=
  S.faithful_points_of_kernel_separation S.point_line_kernel_separation

end Quasithin.I5.DSystem
