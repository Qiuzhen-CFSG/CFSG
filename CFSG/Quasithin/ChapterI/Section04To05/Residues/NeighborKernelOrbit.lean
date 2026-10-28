module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.PointCenterKernel
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.CommonNeighbors

/-!
# The original neighbor kernel moves every distant point

An element of the point core fixing a distant point fixes the unique
common neighbor on each incident line. It fixes that three-point line
pointwise, so it lies in the neighbor kernel. If that kernel were trivial,
the core would act freely on the 32 distant points. D5 would then give a
nontrivial point-group center, already proved to lie in the kernel.
Finally normality in the point group and its distant-point transitivity
show that the nontrivial kernel moves every distant point.

This supplies the group-theoretic obstruction in I.5.13, printed p.423,
without first assuming a size for the nonsingular double-perp set.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem point_core_distant_stabilizer_le_neighborCore (d : S.LocalPolarFacts)
    {y : S.Point} (hxy : ¬ S.Collinear S.basePoint y) :
    S.Q 0 ⊓ MulAction.stabilizer G y ≤ S.neighborCore := by
  intro g hg
  have hgx := S.point_core_fixes_basePoint hg.1
  have hgy : g • y = y := hg.2
  refine ⟨hg.1, (mem_fixingSubgroup_iff G).mpr ?_⟩
  rintro v ⟨l, hxl, hvl⟩
  obtain ⟨u, ⟨hul, hyu⟩, hu⟩ := S.unique_collinear_point_on_line d hxy hxl
  have hgl : g • l = l := S.core_fixes_incident_coset 0 1 (by decide) hg.1 hxl
  have hpres (w : S.Point) : S.Inc w l ↔ S.Inc (g • w) l := by
    constructor
    · intro h
      simpa only [hgl] using h.smul S g
    · intro h
      have hh : g⁻¹ • l = l := by simpa only [inv_smul_smul] using congrArg (g⁻¹ • ·) hgl.symm
      simpa only [hh, inv_smul_smul] using h.smul S g⁻¹
  have hgu : g • u = u := hu _ ⟨(hpres u).mp hul,
    by simpa only [hgy] using hyu.smul S g⟩
  have hxu : S.basePoint ≠ u := fun h => hxy (h.symm ▸ S.collinear_symm hyu)
  exact MulAction.fixes_three_point_set {w : S.Point | S.Inc w l}
    (S.line_points_card l) g hpres hxl hul hxu hgx hgu v hvl

theorem family_normalizes_neighborCore :
    S.family 0 ≤ normalizer (S.neighborCore : Set G) := by
  intro a ha
  apply mem_normalizer_iff.mpr
  intro g
  have hfix : a • S.basePoint = S.basePoint := by
    apply MulAction.mem_stabilizer_iff.mp
    rwa [S.stabilizer_basePoint]
  have hfixi : a⁻¹ • S.basePoint = S.basePoint := by
    simpa only [inv_smul_smul] using congrArg (a⁻¹ • ·) hfix.symm
  have hf (b : G) (hb : b ∈ S.family 0) (hbx : b • S.basePoint = S.basePoint)
      (hbix : b⁻¹ • S.basePoint = S.basePoint) {v : G} (hv : v ∈ S.neighborCore) :
      b * v * b⁻¹ ∈ S.neighborCore := by
    refine ⟨(mem_normalizer_iff.mp (S.family_le_normalizer_Q 0 hb) v).mp hv.1,
      (mem_fixingSubgroup_iff G).mpr ?_⟩
    intro y hy
    have hi : S.Collinear S.basePoint (b⁻¹ • y) := by
      simpa only [hbix] using hy.smul S b⁻¹
    simpa only [mul_smul, smul_inv_smul] using congrArg (b • ·) (S.neighborCore_fixes hv hi)
  constructor
  · exact hf a ha hfix hfixi
  · intro h
    have hh := hf a⁻¹ ((S.family 0).inv_mem ha) hfixi (by simpa only [inv_inv] using hfix) h
    simpa only [inv_inv, ← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel_right, inv_mul_cancel_right] using hh

theorem neighborCore_ne_bot (d : S.LocalPolarFacts) : S.neighborCore ≠ ⊥ := by
  intro hb
  obtain ⟨y, hxy⟩ := S.c3_exists_noncollinear S.basePoint
  let A := {z : S.Point // ¬ S.Collinear S.basePoint z}
  let : Finite A := Nat.finite_of_card_ne_zero (by rw [S.c3_noncollinear_card d S.basePoint]; decide)
  let f : S.Q 0 → A := fun g => ⟨g.val • y, fun h => hxy (by
    have hi := h.smul S g.val⁻¹
    have hgx := S.point_core_fixes_basePoint ((S.Q 0).inv_mem g.property)
    simpa only [hgx, inv_smul_smul] using hi)⟩
  have hf : Function.Injective f := by
    intro g h he
    have hval : g.val • y = h.val • y := congrArg Subtype.val he
    have hfix : (h.val⁻¹ * g.val) • y = y := by
      simpa only [mul_smul, inv_smul_smul] using congrArg (h.val⁻¹ • ·) hval
    have hn := S.point_core_distant_stabilizer_le_neighborCore d hxy
      (show h.val⁻¹ * g.val ∈ S.Q 0 ⊓ MulAction.stabilizer G y from
        ⟨(S.Q 0).mul_mem ((S.Q 0).inv_mem h.property) g.property, hfix⟩)
    rw [hb, mem_bot, inv_mul_eq_one] at hn
    exact Subtype.ext hn.symm
  have hc : Nat.card (S.Q 0) ≤ 32 := by
    have hh := Nat.card_le_card_of_injective f hf
    change Nat.card (S.Q 0) ≤ Nat.card {z : S.Point // ¬ S.Collinear S.basePoint z} at hh
    rwa [S.c3_noncollinear_card d S.basePoint] at hh
  have hc' : Nat.card (pCore 2 (S.family 0)) ≤ 32 := by
    rwa [show Nat.card (S.Q 0) = Nat.card (pCore 2 (S.family 0)) from
      card_map_of_injective (S.family 0).subtype_injective] at hc
  rcases S.nondegenerate rfl with hz | hlarge
  · apply hz
    apply le_bot_iff.mp
    intro a ha
    have hh := S.point_center_mem_neighborCore ha
    rw [hb, mem_bot] at hh
    exact mem_bot.mpr (Subtype.ext hh)
  · omega

theorem neighborCore_moves_distant (d : S.LocalPolarFacts) {y : S.Point}
    (hxy : ¬ S.Collinear S.basePoint y) : ∃ g ∈ S.neighborCore, g • y ≠ y := by
  by_contra! h
  apply S.neighborCore_ne_bot d
  apply le_bot_iff.mp
  intro g hg
  rw [mem_bot]
  let : FaithfulSMul G S.Point := S.faithful_points
  apply eq_of_smul_eq_smul (α := S.Point)
  intro z
  simp only [one_smul]
  by_cases hxz : S.Collinear S.basePoint z
  · exact S.neighborCore_fixes hg hxz
  obtain ⟨a, hax, hay⟩ := S.distant_points_transitive d hxy hxz
  have ha : a ∈ S.family 0 := by
    rw [← S.stabilizer_basePoint]
    exact hax
  have hconj : a⁻¹ * g * a ∈ S.neighborCore := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp (S.family_normalizes_neighborCore ((S.family 0).inv_mem ha)) g).mp hg
  have hh := congrArg (a • ·) (h _ hconj)
  simpa only [mul_smul, smul_inv_smul, hay] using hh

end Quasithin.I5.DSystem
