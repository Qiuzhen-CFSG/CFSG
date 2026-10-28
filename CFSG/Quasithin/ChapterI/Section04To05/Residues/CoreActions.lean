module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.LocalCounts
public import Theory.GroupAction.ThreePointKernelSeparation

/-!
# Original core actions and the unique-line reduction

Each vertex two-core fixes all incident cosets: it is a normal subgroup of
the vertex group contained in every intrinsic parabolic. For the point
core, this supplies the actual action on every three-point incident line.
The separation of its pointwise line kernels then gives the unique-line
assertion of I.5.8, by the elementary three-point permutation argument.

The remaining kernel-separation premise is precisely the source I.5.7
local-core calculation. All line sizes, core actions and translations are
derived here from the original D-system; no recognition conclusion is used.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] {D : Diagram} (S : DSystem D G)

theorem core_fixes_incident_coset (i j : Fin 3) (hji : j ≠ i)
    {g : G} (hg : g ∈ S.Q i) {x : G ⧸ S.family j}
    (hx : S.Inc ((1 : G) : G ⧸ S.family i) x) : g • x = x := by
  obtain ⟨a, ha, rfl⟩ := hg
  have hcore : pCore 2 (S.family i) ≤ (localParabolic S.family i j).normalCore := by
    apply normal_le_normalCore.mpr
    intro b hb
    exact S.T_le j (S.local_core_le_chamber i hb)
  have hk := hcore ha
  rw [Subgroup.normalCore_eq_ker] at hk
  obtain ⟨q, hq⟩ := (S.pointedCosetEquiv i j hji).surjective ⟨x, hx⟩
  have he : a • q = q := Equiv.congr_fun hk q
  have hqv := congrArg Subtype.val hq
  calc
    a.val • x = a.val • (S.pointedCosetEquiv i j hji q).val := congrArg (a.val • ·) hqv.symm
    _ = (S.pointedCosetEquiv i j hji (a • q)).val := (S.pointedCosetEquiv_smul i j hji a q).symm
    _ = x := by rw [he, hqv]

theorem point_core_fixes_basePoint {g : G} (hg : g ∈ S.Q 0) :
    g • S.basePoint = S.basePoint := by
  apply MulAction.mem_stabilizer_iff.mp
  rw [S.stabilizer_basePoint]
  exact (S.family 0).pCoreIn_le 2 hg

theorem unique_base_line_of_kernel_separation
    (hsep : ∀ l m : S.Line, S.Inc S.basePoint l → S.Inc S.basePoint m →
      S.Q 0 ⊓ fixingSubgroup G {z : S.Point | S.Inc z l} =
        S.Q 0 ⊓ fixingSubgroup G {z : S.Point | S.Inc z m} → l = m)
    {y : S.Point} (hy : S.basePoint ≠ y) {l m : S.Line}
    (hxl : S.Inc S.basePoint l) (hyl : S.Inc y l)
    (hxm : S.Inc S.basePoint m) (hym : S.Inc y m) : l = m := by
  apply MulAction.line_unique_of_kernel_separation (fun x l => S.Inc x l) (S.Q 0)
    S.basePoint (fun l _ => S.line_points_card l)
    (fun _ hg => S.point_core_fixes_basePoint hg) _ hsep hy hxl hyl hxm hym
  intro k hxk g hg z
  have hk : g • k = k := S.core_fixes_incident_coset 0 1 (by decide) hg hxk
  constructor
  · intro h
    simpa only [hk] using h.smul S g
  · intro h
    have hk' : g⁻¹ • k = k :=
      (congrArg (g⁻¹ • ·) hk.symm).trans (inv_smul_smul g k)
    simpa only [inv_smul_smul, hk'] using h.smul S g⁻¹

/-- Translated I.5.8(1); the sole remaining premise is source local kernel separation. -/
theorem unique_line_of_kernel_separation
    (hsep : ∀ l m : S.Line, S.Inc S.basePoint l → S.Inc S.basePoint m →
      S.Q 0 ⊓ fixingSubgroup G {z : S.Point | S.Inc z l} =
        S.Q 0 ⊓ fixingSubgroup G {z : S.Point | S.Inc z m} → l = m)
    {x y : S.Point} (hxy : x ≠ y) {l m : S.Line}
    (hxl : S.Inc x l) (hyl : S.Inc y l) (hxm : S.Inc x m) (hym : S.Inc y m) : l = m := by
  obtain ⟨g, hx⟩ := MulAction.exists_smul_eq G S.basePoint x
  apply MulAction.injective g⁻¹
  apply S.unique_base_line_of_kernel_separation hsep
    (y := g⁻¹ • y) (fun he => hxy (by rw [← hx, he, smul_inv_smul]))
  · simpa only [← hx, inv_smul_smul] using hxl.smul S g⁻¹
  · exact hyl.smul S g⁻¹
  · simpa only [← hx, inv_smul_smul] using hxm.smul S g⁻¹
  · exact hym.smul S g⁻¹

end Quasithin.I5.DSystem
