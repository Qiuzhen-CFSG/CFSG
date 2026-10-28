module
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Model.Points
/-!
# Symmetry of the two nonorthogonal marks in 15.3.54

The determinant polar form is invariant under the actual LU-action.
Orthogonality of Z to the conjugate perpendicular would therefore imply
orthogonality of Zᵍ to Z. This proves the reverse disjointness needed to
centralize both W-marks from the single source nonorthogonality hypothesis.

Source: Aschbacher–Smith, 15.3.53–54, printed p.1146, PDF p.1163.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
open Setup ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

private def naturalAction (d : Hypothesis D g) : (D.L ⊔ D.U : Subgroup G) →* MulAut D.VL :=
  D.VL.normalizerMonoidHom.comp (inclusion d.LU_normalizes_VL)

private def pairing (d : Hypothesis D g) (v w : D.VL) : ZMod 2 :=
  (determinantForm (F := ZMod 2)).polarBilin (d.coordinates v).toAdd (d.coordinates w).toAdd

private theorem pairing_symmetric (d : Hypothesis D g) (v w : D.VL) :
    pairing d v w = pairing d w v := by
  exact QuadraticMap.polar_comm _ _ _

private theorem pairing_invariant (d : Hypothesis D g)
    (a : (D.L ⊔ D.U : Subgroup G)) (v w : D.VL) :
    pairing d (naturalAction d a v) (naturalAction d a w) = pairing d v w := by
  have hc (x : D.VL) :
      (d.coordinates (naturalAction d a x)).toAdd =
        matrixAction (d.matrixProjection a) (d.coordinates x).toAdd := by
    have he := d.equivariant a x
    have he' : d.coordinates.symm (Multiplicative.ofAdd
        (matrixAction (d.matrixProjection a) (d.coordinates x).toAdd)) =
        naturalAction d a x := Subtype.ext he
    have hh := congrArg (fun z : D.VL => (d.coordinates z).toAdd) he'
    simpa using hh.symm
  simp only [pairing, hc, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  rw [← map_add, determinantForm_apply, determinantForm_apply, determinantForm_apply,
    matrixAction_det, matrixAction_det, matrixAction_det]
  simp only [determinantForm_apply]

/-- Symmetry of orthogonality uses the actual determinant action and the
book's right conjugates. It is not an independent second nonorthogonality input. -/
theorem point_not_le_conjugate_perpendicular (d : Hypothesis D g) :
    ¬ D.V₁ ≤ conjugate D.V g := by
  intro hle
  apply d.nonorthogonal
  rintro x ⟨z, hz, rfl⟩
  let a : (D.L ⊔ D.U : Subgroup G) := ⟨g, mem_sup_left d.g_mem⟩
  let zv : D.VL := ⟨z, point_le_VL D hz⟩
  let zg := naturalAction d a⁻¹ zv
  change (zg : G) ∈ D.V
  apply (d.perpendicular zg).mpr
  intro w
  have hw : (naturalAction d a (inclusion (point_le_VL D) w) : G) ∈ D.V := by
    obtain ⟨v, hv, he⟩ := hle w.property
    change g⁻¹ * v * (g⁻¹)⁻¹ = (w : G) at he
    change g * (w : G) * g⁻¹ ∈ D.V
    have he' : g * (w : G) * g⁻¹ = v := by rw [← he]; group
    rw [he']
    exact hv
  have hp := (d.perpendicular (naturalAction d a (inclusion (point_le_VL D) w))).mp hw ⟨z,hz⟩
  change pairing d (naturalAction d a (inclusion (point_le_VL D) w)) zv = 0 at hp
  change pairing d zg (inclusion (point_le_VL D) w) = 0
  rw [pairing_symmetric]
  have he := pairing_invariant d a (inclusion (point_le_VL D) w) zg
  have hh : naturalAction d a zg = zv := by
    change naturalAction d a (naturalAction d a⁻¹ zv) = zv
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  rw [hh] at he
  exact he.symm.trans hp

/-- The reverse point/hyperplane intersection, deduced from nonorthogonality. -/
theorem point_inf_conjugate_perpendicular (d : Hypothesis D g) :
    D.V₁ ⊓ conjugate D.V g = ⊥ := by
  obtain ⟨z, hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : D.V₁)).mp d.point_card
  apply eq_bot_iff.mpr
  intro x hx
  change x = 1
  by_contra hne
  apply point_not_le_conjugate_perpendicular d
  intro y hy
  by_cases hy1 : y = 1
  · exact hy1 ▸ (conjugate D.V g).one_mem
  · have he : x = y := congrArg Subtype.val
      ((huniq (⟨x,hx.1⟩ : D.V₁) (fun he => hne (congrArg Subtype.val he))).trans
        (huniq (⟨y,hy⟩ : D.V₁) (fun he => hy1 (congrArg Subtype.val he))).symm)
    exact he ▸ hx.2
end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
