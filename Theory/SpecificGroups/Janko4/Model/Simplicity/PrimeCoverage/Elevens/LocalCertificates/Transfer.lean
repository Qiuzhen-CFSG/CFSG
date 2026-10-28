module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates.Relations
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates.OrbitCertificates
import Mathlib.Tactic.FinCases

/-!
# Transfer of eleven-coordinate certificates to a group

A homomorphism taking `X,Y,Z` to `x,y,[x,y]` has image exactly `⟨x,y⟩`.
If it is injective, that subgroup has order 1331. The six normalizer identities
realize every word in the four coordinate actions by conjugation in the target
group. Applying the kernel-checked coordinate orbit certificates then covers
every nonidentity element of the image by the central or noncentral cyclic
representative. No property of the concrete J₄ matrices is assumed implicitly.
-/

public section

namespace Janko4.Simplicity.Elevens
open LocalCoordinates
variable {G : Type*} [Group G]

theorem coordinate_range (f : Coord →* G) (x y z : G)
    (hX : f X = x) (hY : f Y = y) (hZ : f Z = z)
    (hz : x⁻¹ * y⁻¹ * x * y = z) : f.range = Subgroup.closure {x, y} := by
  apply le_antisymm
  · rintro w ⟨c, rfl⟩
    rw [← normal_form c, map_mul, map_mul, map_pow, map_pow, map_pow, hX, hY, hZ]
    have hx : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
    have hy : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
    have hzmem : z ∈ Subgroup.closure ({x, y} : Set G) := by
      rw [← hz]
      exact mul_mem (mul_mem (mul_mem (inv_mem hx) (inv_mem hy)) hx) hy
    exact mul_mem (mul_mem (pow_mem hx _) (pow_mem hy _)) (pow_mem hzmem _)
  · apply (Subgroup.closure_le f.range).mpr
    intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · exact ⟨X, hX⟩
    · have : w = y := Set.mem_singleton_iff.mp hw
      subst w
      exact ⟨Y, hY⟩

theorem coordinate_card (f : Coord →* G) (hf : Function.Injective f) (x y z : G)
    (hX : f X = x) (hY : f Y = y) (hZ : f Z = z)
    (hz : x⁻¹ * y⁻¹ * x * y = z) : Nat.card (Subgroup.closure {x, y}) = 1331 := by
  rw [← coordinate_range f x y z hX hY hZ hz]
  have hbij : Function.Bijective f.rangeRestrict :=
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr hf, f.rangeRestrict_surjective⟩
  exact (Nat.card_congr (Equiv.ofBijective f.rangeRestrict hbij)).symm.trans card_coord

theorem realize_actions (f : Coord →* G) (u v x y z : G)
    (hX : f X = x) (hY : f Y = y) (hZ : f Z = z)
    (h : ElevenNormalizerRelations u v x y z) :
    ∀ s : Fin 4, ∃ g : G, ∀ c : Coord, f (action s c) = g * f c * g⁻¹ := by
  have hu : f.comp actUHom = (MulAut.conj u⁻¹).toMonoidHom.comp f := by
    apply LocalCoordinates.hom_ext
    · simpa only [MonoidHom.comp_apply, actU_X, map_mul, map_pow, hX, hY, hZ,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using h.ux.symm
    · simpa only [MonoidHom.comp_apply, actU_Y, map_mul, map_pow, hX, hY, hZ,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using h.uy.symm
    · simpa only [MonoidHom.comp_apply, actU_Z, hX, hY, hZ,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using h.uz.symm
  have hv : f.comp actVHom = (MulAut.conj v⁻¹).toMonoidHom.comp f := by
    apply LocalCoordinates.hom_ext
    · simpa only [MonoidHom.comp_apply, actV_X, hX, hY,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using h.vx.symm
    · simpa only [MonoidHom.comp_apply, actV_Y, map_mul, map_pow, hX, hY, hZ,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using h.vy.symm
    · simpa only [MonoidHom.comp_apply, actV_Z, map_pow, hZ,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using h.vz.symm
  intro s
  fin_cases s
  · refine ⟨u⁻¹, ?_⟩
    intro c
    exact DFunLike.congr_fun hu c
  · refine ⟨v⁻¹, ?_⟩
    intro c
    exact DFunLike.congr_fun hv c
  · refine ⟨x⁻¹, ?_⟩
    intro c
    change f (actX c) = _
    rw [actX_eq, map_mul, map_mul, map_inv, hX, inv_inv]
  · refine ⟨y⁻¹, ?_⟩
    intro c
    change f (actY c) = _
    rw [actY_eq, map_mul, map_mul, map_inv, hY, inv_inv]

theorem realize_words (f : Coord →* G)
    (h : ∀ s : Fin 4, ∃ g : G, ∀ c : Coord, f (action s c) = g * f c * g⁻¹)
    (l : List (Fin 4)) : ∃ g : G, ∀ c : Coord, f (wordHom l c) = g * f c * g⁻¹ := by
  induction l with
  | nil => exact ⟨1, by intro c; simp [wordHom]⟩
  | cons s l ih =>
    obtain ⟨g, hg⟩ := h s
    obtain ⟨k, hk⟩ := ih
    refine ⟨k*g, ?_⟩
    intro c
    change f (wordHom l (action s c)) = _
    rw [hk, hg]
    simp only [mul_inv_rev, mul_assoc]


theorem coordinate_coverage (f : Coord →* G) (u v x y z : G)
    (hX : f X = x) (hY : f Y = y) (hZ : f Z = z)
    (hz : x⁻¹ * y⁻¹ * x * y = z)
    (h : ElevenNormalizerRelations u v x y z)
    (w : G) (hw : w ∈ Subgroup.closure {x, y}) (hw1 : w ≠ 1) :
    ∃ (j : Fin 2) (n : ℕ) (g : G), ![z, x] j = g * w ^ n * g⁻¹ := by
  rw [← coordinate_range f x y z hX hY hZ hz] at hw
  obtain ⟨c, rfl⟩ := hw
  have hc : c ≠ 1 := by
    intro hc
    exact hw1 (hc ▸ f.map_one)
  obtain ⟨j, n, l, hrep⟩ := LocalCoordinates.cyclic_coverage c hc
  obtain ⟨g, hg⟩ := realize_words f (realize_actions f u v x y z hX hY hZ h) l
  refine ⟨j, n, g, ?_⟩
  have hr : f (representative j) = ![z, x] j := by
    fin_cases j
    · exact hZ
    · exact hX
  rw [← hr, hrep, hg, map_pow]

end Janko4.Simplicity.Elevens
