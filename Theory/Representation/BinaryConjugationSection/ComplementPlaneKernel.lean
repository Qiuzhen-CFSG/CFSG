module
public import Theory.Representation.BinaryConjugationSection.ComplementPlaneGeneration
public import Theory.Representation.BinaryConjugationSection.InvariantImages
import Mathlib.Tactic.FinCases

/-!
# Exact plane kernels under a complementary cubic

The cubic fixing a marked plane acts irreducibly on the complementary binary
plane. A stable subspace containing the fixed plane is therefore that plane
or the whole four-space. Through literal conjugation coordinates this gives
U intersect N = V₃ whenever N contains V₃, is normalized by the cubic actor,
and does not contain U. The original coordinate kernel V₁ is retained.

Source application: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.30, printed p.964: the selected maximal kernel meets U_H exactly in V₃.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
namespace Representation.BinaryConjugationSection
open BinaryParabolicExteriorSquare.PlaneSpan BinaryLinear.FlagCoordinates

private theorem cubic_plane_dichotomy
    (P : Submodule (ZMod 2) (Fin 4 → ZMod 2)) (hp : plane ≤ P)
    (hc : ∀ x ∈ P, Matrix.mulVec complementCubic x ∈ P) : P = plane ∨ P = ⊤ := by
  by_cases hle : P ≤ plane
  · exact Or.inl (le_antisymm hle hp)
  · right
    obtain ⟨x,hx,hxp⟩ := Set.not_subset.mp hle
    have hx' : x 2 ≠ 0 ∨ x 3 ≠ 0 := by
      change ¬ (x 2 = 0 ∧ x 3 = 0) at hxp
      tauto
    apply top_unique
    intro w _
    have coeff : ∀ x₂ x₃ : ZMod 2, x₂ ≠ 0 ∨ x₃ ≠ 0 →
        ∀ w₂ w₃ : ZMod 2, ∃ a b : ZMod 2,
          a*x₂ + b*x₃ = w₂ ∧ a*x₃ + b*(x₂+x₃) = w₃ := by decide
    obtain ⟨a,b,h2,h3⟩ := coeff (x 2) (x 3) hx' (w 2) (w 3)
    have hv : a • x + b • Matrix.mulVec complementCubic x ∈ P :=
      P.add_mem (P.smul_mem a hx) (P.smul_mem b (hc x hx))
    have hz : w - (a • x + b • Matrix.mulVec complementCubic x) ∈ plane := by
      change (w 2 - (a*x 2+b*(Matrix.mulVec complementCubic x) 2) = 0) ∧
        (w 3 - (a*x 3+b*(Matrix.mulVec complementCubic x) 3) = 0)
      constructor
      · simpa [complementCubic,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
          using (show w 2 - (a*x 2+b*x 3) = 0 by rw [h2,sub_self])
      · simpa [complementCubic,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
          using (show w 3 - (a*x 3+b*(x 2+x 3)) = 0 by rw [h3,sub_self])
    simpa only [sub_add_cancel] using P.add_mem (hp hz) hv

variable {G : Type*} [Group G]

/-- The original cubic and properness determine the entire intersection. -/
theorem inf_eq_plane_of_complement
    (H D U V1 V3 N : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H U V1 ρ)
    (π : H →* SL(4,ZMod 2))
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (h13 : V1 ≤ V3) (h3U : V3 ≤ U) (hplane : d.imageSpace V3 = plane)
    (hcubic : complementElement ∈ (D.subgroupOf H).map π)
    (hDN : D ≤ normalizer N) (h3N : V3 ≤ N) (hUN : ¬ U ≤ N) :
    U ⊓ N = V3 := by
  obtain ⟨a,ha,he⟩ := hcubic
  have hp : plane ≤ d.imageSpace N := hplane ▸ d.imageSpace_mono h3N
  have hc : ∀ x ∈ d.imageSpace N, Matrix.mulVec complementCubic x ∈ d.imageSpace N := by
    intro x hx
    have hh := d.imageSpace_apply_mem N a (hDN ha) x hx
    rwa [hnatural,he] at hh
  rcases cubic_plane_dichotomy (d.imageSpace N) hp hc with heq | heq
  · apply le_antisymm ?_ (le_inf h3U h3N)
    intro x hx
    have hm : (d.coordinates ⟨x,hx.1⟩).toAdd ∈ d.imageSpace V3 := by
      rw [hplane,←heq]
      exact (d.mem_imageSpace_iff N _).mpr ⟨⟨x,hx.1⟩,hx.2,rfl⟩
    exact (d.coordinates_mem_imageSpace_iff_of_kernel_le V3 h13 ⟨x,hx.1⟩).mp hm
  · exact (hUN ((d.le_sup_kernel_of_image_top N heq).trans
      (sup_le le_rfl (h13.trans h3N)))).elim
end Representation.BinaryConjugationSection
