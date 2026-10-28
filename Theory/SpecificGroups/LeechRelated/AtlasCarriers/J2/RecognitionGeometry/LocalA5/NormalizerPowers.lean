module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.Seed

/-!
# Normalization of an order-three subgroup

The normalizer sends a generator to one of its two nonidentity powers.
This converts membership in the literal endpoint normalizers into the
two scalar alternatives used by the concrete local certificates.
-/

public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
open Subgroup

theorem normalizer_three_power {u g : Carrier} (hu : orderOf u = 3)
    (hg : g ∈ normalizer (zpowers u : Set Carrier)) :
    ∃ i : Fin 2, g * u = u ^ (i.val + 1) * g := by
  classical
  have hv : MulAut.conj g u ∈ zpowers u :=
    (mem_normalizer_iff.mp hg u).mp (mem_zpowers u)
  have hu1 : u ≠ 1 := by intro h; simp [h] at hu
  have hv1 : MulAut.conj g u ≠ 1 :=
    fun h => hu1 ((MulAut.conj g).injective (h.trans (map_one _).symm))
  rw [mem_zpowers_iff_mem_range_orderOf, hu, Finset.mem_image] at hv
  obtain ⟨n, hn, he⟩ := hv
  have hn3 : n < 3 := Finset.mem_range.mp hn
  have hn0 : n ≠ 0 := by intro h; apply hv1; rw [← he, h, pow_zero]
  refine ⟨⟨n - 1, by omega⟩, ?_⟩
  dsimp
  rw [show n - 1 + 1 = n by omega, he]
  simp only [MulAut.conj_apply, inv_mul_cancel_right]

end Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
