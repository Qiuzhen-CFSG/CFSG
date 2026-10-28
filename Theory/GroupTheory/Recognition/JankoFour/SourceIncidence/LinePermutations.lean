module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LineAction
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PointChart
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Geometry
public import Mathlib.Logic.Equiv.Fintype

/-!
# Literal line permutations and the collinear triangle branch

The original S factor induces every permutation of the five points on a line
and fixes all seven planes on it. Conjugating by the same line representative
retains both actions simultaneously. Extending a permutation of three distinct
points to the line proves the collinear branch of AS91 (5.6)(2).
The zero native orbital is also identified with equality of incident lines,
using exactly the unchanged transported definition in SourceCycleBase.Input.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (5.1)(1), (5.4)(2),
and the collinear case of (5.6)(2), pp.599–601, DOI 10.1007/BF01232280.
-/

public section
open Subgroup
open scoped Pointwise Matrix
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)

/-- The original line chart transported by its left-coset representative. -/
noncomputable def linePointsAt (l : Line a.L) :
    {x : Point a.P // OnLine a.L x l} ≃ a.LinePoints where
  toFun x := ⟨(representative l)⁻¹ • x.val,by
    have hh := incident_smul (representative l)⁻¹ x.property
    have he : (representative l)⁻¹ • l = Cosets.vertex a.L.G₂ 1 := by
      calc
        _ = (representative l)⁻¹ • Cosets.vertex a.L.G₂ (representative l) :=
          congrArg ((representative l)⁻¹ • ·) (vertex_representative l).symm
        _ = _ := by rw [Cosets.smul_vertex,inv_mul_cancel]
    rw [he] at hh
    exact hh⟩
  invFun x := ⟨representative l • x.val,by
    have hh := incident_smul (representative l) x.property
    rw [Cosets.smul_vertex,mul_one,vertex_representative] at hh
    exact hh⟩
  left_inv x := Subtype.ext (smul_inv_smul _ _)
  right_inv x := Subtype.ext (inv_smul_smul _ _)

/-- Every permutation of a line's five points is realized while fixing every
plane on that line. This uses the same section-four S factor. -/
theorem line_permutations (l : Line a.L)
    (p : Equiv.Perm {x : Point a.P // OnLine a.L x l}) :
    ∃ g : G, g • l = l ∧
      (∀ π, LineOnPlane a.L l π → g • π = π) ∧
      ∀ x : {x : Point a.P // OnLine a.L x l}, g • x.val = (p x).val := by
  let e := a.linePointsAt l
  obtain ⟨s,n,hns,hn⟩ := a.exists_S_linePointAction ((e.symm.trans p).trans e)
  let r := representative l
  refine ⟨r*(n : G)*r⁻¹,?_,?_,?_⟩
  · have hnfix : (n : G) • Cosets.vertex a.L.G₂ 1 = Cosets.vertex a.L.G₂ 1 := by
      rw [Cosets.smul_vertex,mul_one,(Cosets.vertex_eq_base _ _).mpr n.property]
    have hr : r • Cosets.vertex a.L.G₂ 1 = l := by
      rw [Cosets.smul_vertex,mul_one,vertex_representative]
    rw [←hr,mul_smul,mul_smul,inv_smul_smul,hnfix]
  · intro π hπ
    have hbase : LineOnPlane a.L (Cosets.vertex a.L.G₂ 1) (r⁻¹ • π) := by
      have hh := incident_smul r⁻¹ hπ
      have he : r⁻¹ • l = Cosets.vertex a.L.G₂ 1 := by
        rw [←vertex_representative l,Cosets.smul_vertex,inv_mul_cancel]
      rw [he] at hh
      exact hh
    have hfix := (a.plane_action_kernel n).mpr (hns.symm ▸ s.property) (r⁻¹ • π) hbase
    rw [mul_smul,mul_smul,hfix,smul_inv_smul]
  · intro x
    have hh := congrArg Subtype.val (Equiv.congr_fun hn (e x))
    rw [a.linePointAction_apply] at hh
    simp only [Equiv.trans_apply,Equiv.symm_apply_apply] at hh
    have he : (n : G) • (r⁻¹ • x.val) = r⁻¹ • (p x).val := by
      exact hh
    simpa only [mul_smul,smul_inv_smul] using congrArg (r • ·) he

/-- The collinear branch of AS91 (5.6)(2), with all three marked points and
any incident plane retained. -/
theorem collinear_triple_permutations (l : Line a.L) (v : Fin 3 → Point a.P)
    (hv : Function.Injective v) (hl : ∀ i, OnLine a.L (v i) l)
    (σ : Equiv.Perm (Fin 3)) :
    ∃ g : G, g • l = l ∧ (∀ π, LineOnPlane a.L l π → g • π = π) ∧
      ∀ i : Fin 3, g • v i = v (σ i) := by
  classical
  let f : Fin 3 ↪ {x : Point a.P // OnLine a.L x l} :=
    ⟨fun i => ⟨v i,hl i⟩,fun _ _ he => hv (congrArg Subtype.val he)⟩
  obtain ⟨g,hg,hπ,hv⟩ := a.line_permutations l (σ.viaFintypeEmbedding f)
  refine ⟨g,hg,hπ,fun i => ?_⟩
  have hh := hv (f i)
  rw [Equiv.Perm.viaFintypeEmbedding_apply_image] at hh
  exact hh

/-- The zero orbital is exactly equality of incident lines, using the
original unchanged transported native definition. -/
theorem delta_zero (x : Point a.P) (l k : Line a.L) :
    LineType a.residueChart 0 x l k ↔ OnLine a.L x l ∧ k = l := by
  constructor
  · rintro ⟨g,b,c,rfl,rfl,rfl,he⟩
    have hc : c = b := a.residueChart.lines.injective
      (Native.line_parts_injective (show (a.residueChart.lines c).parts =
        (a.residueChart.lines b).parts from he.symm))
    refine ⟨?_,congrArg (fun t => g • t.val) hc⟩
    simpa only [OnLine,Cosets.smul_vertex,mul_one] using incident_smul g b.property
  · rintro ⟨hxl,rfl⟩
    obtain ⟨g,rfl,rfl⟩ := hxl
    let b : {l : Line a.L // OnLine a.L (Cosets.vertex a.P.M 1) l} :=
      ⟨Cosets.vertex a.L.G₂ 1,⟨1,rfl,rfl⟩⟩
    exact ⟨g,b,b,rfl,by simp [b,Cosets.smul_vertex],by simp [b,Cosets.smul_vertex],rfl⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
