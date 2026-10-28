module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.DoubleCosetCover.SectorGeometry
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.DoubleCosetCover.SeedStabilizer.Witnesses

/-!
# The exact Rudvalis seed stabilizer

Seed-profile multiplicities and certified orbital refinements constrain the
images of points 0 and 1. Explicit max4 words match these images in turn.
The remaining element fixes the five-point model base and is the identity.
Together with generator invariance of the seed this identifies its full
setwise stabilizer, without a global sector cover or an order bound.

Source application: Aschbacher--Smith, printed p.511 (PDF p.528), citing
Aschbacher (1986), no.343. The precise 28-set is the zero-based seed retained
in `Representatives/source/Generate.py` and defined in `SectorGeometry`.
-/

namespace Rudvalis.SylowOvergroups.TwoCore.Generation.DoubleCosetCover
open SeedStabilizerCertificate

private theorem fix_zero_mem_max4 (g : Model) (hg : g ∈ seedStabilizer)
    (hg0 : g • (0 : Fin 4060) = 0) : g ∈ max4 := by
  have hf : ∀ x : Fin 4060, x.val < 1 → g • x = x := by
    intro x hx
    have he : x = 0 := Fin.ext (by change x.val = 0; omega)
    subst x
    exact hg0
  obtain ⟨h, hh, hh0, hh1⟩ := image_one g hg hf
  have hq : h⁻¹ * g ∈ seedStabilizer :=
    seedStabilizer.mul_mem (seedStabilizer.inv_mem (max4_le_seedStabilizer hh)) hg
  have hfix : ∀ x : Fin 4060, x.val < 2 → (h⁻¹ * g) • x = x := by
    intro x hx
    rw [mul_smul]
    apply inv_smul_eq_iff.mpr
    have he : x = 0 ∨ x = 1 := by
      have : x.val = 0 ∨ x.val = 1 := by omega
      simpa only [Fin.ext_iff, Fin.val_zero, Fin.val_one] using this
    rcases he with rfl | rfl
    · exact hg0.trans hh0.symm
    · exact hh1.symm
  have he := fix_two_eq_one (h⁻¹ * g) hq hfix
  have : h = g := inv_mul_eq_one.mp he
  exact this ▸ hh

/-- Every model element preserving the exact 28-set lies in max4. -/
public theorem seedStabilizer_le_max4 : seedStabilizer ≤ max4 := by
  intro g hg
  obtain ⟨h, hh, hh0⟩ := image_zero g hg
  have hq : h⁻¹ * g ∈ seedStabilizer :=
    seedStabilizer.mul_mem (seedStabilizer.inv_mem (max4_le_seedStabilizer hh)) hg
  have hq0 : (h⁻¹ * g) • (0 : Fin 4060) = 0 := by
    rw [mul_smul, ← hh0, inv_smul_smul]
  have hm := max4.mul_mem hh (fix_zero_mem_max4 (h⁻¹ * g) hq hq0)
  simpa only [mul_inv_cancel_left] using hm

/-- The actual setwise stabilizer of the seed is the fourth ATLAS subgroup. -/
public theorem seedStabilizer_eq_max4 : seedStabilizer = max4 :=
  le_antisymm seedStabilizer_le_max4 max4_le_seedStabilizer

end Rudvalis.SylowOvergroups.TwoCore.Generation.DoubleCosetCover
