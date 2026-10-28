module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.CoreTransitivity
public import Mathlib.Data.Fintype.Sigma

/-!
# The thirty original neighbors of a C₃ point

Unique lines identify the neighbors of a point with pairs consisting of
one of its fifteen incident lines and one of that line's two other points.
This gives thirty neighbors. The original point group is transitive on
them: it transports their lines and the point core adjusts the second point.

Source: I.5.9(1), printed p.421. No global point count is assumed.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem line_other_points_card {x : S.Point} {l : S.Line} (hx : S.Inc x l) :
    Nat.card {y : S.Point // S.Inc y l ∧ x ≠ y} = 2 := by
  classical
  let A := {y : S.Point // S.Inc y l}
  let : Finite A := Nat.finite_of_card_ne_zero (by rw [S.line_points_card l]; decide)
  let := Fintype.ofFinite A
  let a : A := ⟨x, hx⟩
  let e : {y : S.Point // S.Inc y l ∧ x ≠ y} ≃ {y : A // ¬ y = a} := {
    toFun y := ⟨⟨y.val, y.property.1⟩, fun h => y.property.2 (congrArg Subtype.val h).symm⟩
    invFun y := ⟨y.val.val, y.val.property, fun h => y.property (Subtype.ext h.symm)⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]
  have h : Fintype.card A = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact S.line_points_card l
  omega

def NeighborFlag (x : S.Point) :=
  Σ l : {l : S.Line // S.Inc x l}, {y : S.Point // S.Inc y l.val ∧ x ≠ y}

def neighborFlagEquiv (x : S.Point) :
    S.NeighborFlag x ≃ {y : S.Point // x ≠ y ∧ S.Collinear x y} := by
  let f : S.NeighborFlag x → {y : S.Point // x ≠ y ∧ S.Collinear x y} :=
    fun p => ⟨p.2.val, p.2.property.2, p.1.val, p.1.property, p.2.property.1⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨l, y⟩ ⟨m, z⟩ h
    have hyv : y.val = z.val := congrArg Subtype.val h
    have hlm : l = m := Subtype.ext (S.unique_line y.property.2 l.property y.property.1
      m.property (hyv.symm ▸ z.property.1))
    subst m
    have hyz : y = z := Subtype.ext hyv
    exact congrArg (Sigma.mk l) hyz
  · rintro ⟨y, hxy, l, hxl, hyl⟩
    exact ⟨⟨⟨l, hxl⟩, ⟨y, hyl, hxy⟩⟩, rfl⟩

/-- I.5.9(1): the exact neighbor count in the original geometry. -/
theorem c3_neighbors_card (x : S.Point) :
    Nat.card {y : S.Point // x ≠ y ∧ S.Collinear x y} = 30 := by
  classical
  let A := {l : S.Line // S.Inc x l}
  let : Finite A := Nat.finite_of_card_ne_zero (by rw [S.c3_point_lines_card x]; decide)
  let := Fintype.ofFinite A
  let (l : A) : Finite {y : S.Point // S.Inc y l.val ∧ x ≠ y} :=
    Nat.finite_of_card_ne_zero (by rw [S.line_other_points_card l.property]; decide)
  rw [← Nat.card_congr (S.neighborFlagEquiv x)]
  change Nat.card (Σ l : A, {y : S.Point // S.Inc y l.val ∧ x ≠ y}) = 30
  rw [Nat.card_sigma]
  have h : Fintype.card A = 15 := by
    rw [← Nat.card_eq_fintype_card]
    exact S.c3_point_lines_card x
  calc
    _ = ∑ _l : A, 2 := by
      apply Finset.sum_congr rfl
      intro l _
      exact S.line_other_points_card l.property
    _ = Fintype.card A * 2 := by simp
    _ = 30 := by rw [h]

theorem base_neighbors_transitive {y z : S.Point}
    (hy : S.Collinear S.basePoint y) (hz : S.Collinear S.basePoint z)
    (hxy : S.basePoint ≠ y) (hxz : S.basePoint ≠ z) :
    ∃ g ∈ S.family 0, g • y = z := by
  obtain ⟨l, hxl, hyl⟩ := hy
  obtain ⟨m, hxm, hzm⟩ := hz
  obtain ⟨a, ha, hal⟩ := (CosetGeometry.incident_base_iff S.family 0 ⟨1, l⟩).mp hxl
  obtain ⟨b, hb, hbm⟩ := (CosetGeometry.incident_base_iff S.family 0 ⟨1, m⟩).mp hxm
  have hl : a • S.baseLine = l := by
    change ((a * 1 : G) : G ⧸ S.family 1) = l
    simpa only [mul_one] using hal
  have hm : b • S.baseLine = m := by
    change ((b * 1 : G) : G ⧸ S.family 1) = m
    simpa only [mul_one] using hbm
  have hpa : a • S.basePoint = S.basePoint := by
    apply MulAction.mem_stabilizer_iff.mp
    rwa [S.stabilizer_basePoint]
  have hpb : b • S.basePoint = S.basePoint := by
    apply MulAction.mem_stabilizer_iff.mp
    rwa [S.stabilizer_basePoint]
  have hy' : S.Inc (a⁻¹ • y) S.baseLine := by
    simpa only [← hl, inv_smul_smul] using hyl.smul S a⁻¹
  have hz' : S.Inc (b⁻¹ • z) S.baseLine := by
    simpa only [← hm, inv_smul_smul] using hzm.smul S b⁻¹
  obtain ⟨q, hq, he⟩ := S.point_core_baseLine_transitive hy' hz'
    (fun h => hxy (by simpa only [hpa, smul_inv_smul] using congrArg (a • ·) h))
    (fun h => hxz (by simpa only [hpb, smul_inv_smul] using congrArg (b • ·) h))
  refine ⟨b * q * a⁻¹, (S.family 0).mul_mem
    ((S.family 0).mul_mem hb ((S.family 0).pCoreIn_le 2 hq)) ((S.family 0).inv_mem ha), ?_⟩
  simpa only [mul_smul, smul_inv_smul] using congrArg (b • ·) he

end Quasithin.I5.DSystem
