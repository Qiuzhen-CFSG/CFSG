module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Model.Images

/-!
# Marked points for the determinant calculation in G.2.6

The fixed-point equations use the original star projection and the given
coordinates on V_L. Every element of the marked U-image fixes the marked
point, since the H-closure U centralizes V₁. Nonorthogonality makes the
conjugate order-two point disjoint from V, hence from the original point.
These statements retain the right-conjugation convention of the source.

Source: Aschbacher–Smith, G.2.6, printed p.336, and the nonorthogonal
marked points used in 15.3.54, printed p.1146.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G]

private theorem inf_eq_bot_of_card_two {A B : Subgroup G}
    (hcard : Nat.card A = 2) (hn : ¬ A ≤ B) : A ⊓ B = ⊥ := by
  obtain ⟨z, hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hcard
  apply eq_bot_iff.mpr
  intro x hx
  change x = 1
  by_contra hne
  apply hn
  intro y hy
  by_cases hy1 : y = 1
  · exact hy1 ▸ B.one_mem
  · have hxy : (⟨x, hx.1⟩ : A) = ⟨y, hy⟩ :=
      (huniq _ (fun he => hne (congrArg Subtype.val he))).trans
        (huniq _ (fun he => hy1 (congrArg Subtype.val he))).symm
    have he : x = y := congrArg Subtype.val hxy
    rw [← he]
    exact hx.2

namespace Hypothesis
variable [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)
include d

/-- Coordinates of the actual marked point, with its subgroup inclusion retained. -/
def pointVector (z : D.V₁) : Mat (F := ZMod 2) :=
  (d.coordinates (inclusion (point_le_VL D) z)).toAdd

theorem pointVector_injective : Function.Injective d.pointVector := by
  intro z w he
  apply inclusion_injective (point_le_VL D)
  apply d.coordinates.injective
  exact Multiplicative.toAdd.injective he

theorem pointVector_eq_zero_iff (z : D.V₁) : d.pointVector z = 0 ↔ z = 1 := by
  have hzero : d.pointVector 1 = 0 := by simp [pointVector]
  rw [← hzero, d.pointVector_injective.eq_iff]

theorem exists_pointVector_ne_zero : ∃ z : D.V₁, d.pointVector z ≠ 0 := by
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : D.V₁)).mp d.point_card
  exact ⟨z, fun he => hz ((d.pointVector_eq_zero_iff z).mp he)⟩

/-- The full pointwise stabilizer in the actual determinant group. -/
def pointStabilizer : Subgroup (PairSL (F := ZMod 2)) :=
  ⨅ z : D.V₁, (MulAction.stabilizer
    (Mat (F := ZMod 2) ≃ₗ[ZMod 2] Mat (F := ZMod 2)) (d.pointVector z)).comap matrixHom

theorem mem_pointStabilizer (a : PairSL (F := ZMod 2)) :
    a ∈ d.pointStabilizer ↔ ∀ z : D.V₁, matrixAction a (d.pointVector z) = d.pointVector z := by
  simp only [pointStabilizer, mem_iInf, mem_comap, MulAction.mem_stabilizer_iff]
  rfl

/-- The marked U-image fixes the source point; equality with its full
stabilizer still requires the singular-point calculation. -/
theorem modelImage_U_le_pointStabilizer : d.modelImage D.U ≤ d.pointStabilizer := by
  rintro a ⟨u, hu, rfl⟩
  rw [d.mem_pointStabilizer]
  intro z
  let v : D.VL := inclusion (point_le_VL D) z
  have hconj : (u : G) * v * (u : G)⁻¹ = (v : G) := by
    have hc := d.base.U_le_centralizer_point hu z z.property
    change (z : G) * (u : G) = (u : G) * z at hc
    change (u : G) * (z : G) * (u : G)⁻¹ = z
    rw [← hc, mul_inv_cancel_right]
  have he := d.equivariant u v
  have he' : d.coordinates.symm (Multiplicative.ofAdd
      (matrixAction (d.matrixProjection u) (d.coordinates v).toAdd)) = v :=
    Subtype.ext (he.trans hconj)
  have hc := congrArg (fun w : D.VL => (d.coordinates w).toAdd) he'
  simpa [pointVector, v] using hc

/-- The original g does not normalize the marked point. -/
theorem g_not_normalizes_point : g ∉ D.G₁ := by
  intro hg
  have he : conjugate D.V₁ g = D.V₁ :=
    mem_normalizer_iff_map_conj_eq.mp (D.G₁.inv_mem hg)
  exact d.nonorthogonal (he.symm ▸ d.base.point_le)

/-- The nonorthogonal conjugate point has trivial intersection with V. -/
theorem conjugate_point_inf_V : conjugate D.V₁ g ⊓ D.V = ⊥ := by
  apply inf_eq_bot_of_card_two _ d.nonorthogonal
  rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective]
  exact d.point_card

/-- In particular the two source-marked point subgroups are disjoint. -/
theorem point_inf_conjugate_point : D.V₁ ⊓ conjugate D.V₁ g = ⊥ := by
  apply eq_bot_iff.mpr
  calc
    D.V₁ ⊓ conjugate D.V₁ g ≤ D.V ⊓ conjugate D.V₁ g := inf_le_inf_right _ d.base.point_le
    _ = ⊥ := by rw [inf_comm, d.conjugate_point_inf_V]

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
