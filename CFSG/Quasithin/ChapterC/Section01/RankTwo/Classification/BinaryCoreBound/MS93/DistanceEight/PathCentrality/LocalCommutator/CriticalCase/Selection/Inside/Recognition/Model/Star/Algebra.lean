module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Model.Star.Core
/-!
# Central differences on a binary seed line

An invariant seed of index two over the common core is fixed modulo the core.
Once the core is fixed by the full actor, displacement at a seed vector defines
a homomorphism from its marked stabilizer to the elementary abelian carrier.
Elements of order three have zero displacement. These facts retain the actual
vectors in the original carrier, so they apply to nonsplit extensions.

Source: the index-two branch of MS93 (1.6), printed pp.845–847.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
open Escape.Initial.Natural.Splitting
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [Group E] [IsElementaryAbelian 2 E]

/-- An invariant binary line over the common core is fixed modulo that core. -/
theorem seed_difference_mem_core (ρ : SL →* MulAut E)
    (d : EscapingConfiguration ρ) (hline : (actionOrbitCore ρ d.seed).relIndex d.seed = 2)
    (k : SL) (hk : k ∈ markedPointStabilizer d.marking d.point)
    (w : E) (hw : w ∈ d.seed) : w⁻¹ * ρ k w ∈ actionOrbitCore ρ d.seed := by
  have hkw : ρ k w ∈ d.seed := by
    rw [← d.invariant k hk]
    exact mem_map_of_mem _ hw
  have hiff : ρ k w ∈ actionOrbitCore ρ d.seed ↔ w ∈ actionOrbitCore ρ d.seed := by
    conv_lhs => rw [← actionOrbitCore_map ρ d.seed k]
    exact mem_map_iff_mem (ρ k).injective
  let h := (actionOrbitCore ρ d.seed).subgroupOf d.seed
  exact (h.mul_mem_iff_of_index_two hline (a := (⟨w,hw⟩ : d.seed)⁻¹)
    (b := ⟨ρ k w,hkw⟩)).mpr (by
      change w⁻¹ ∈ actionOrbitCore ρ d.seed ↔ ρ k w ∈ actionOrbitCore ρ d.seed
      rw [inv_mem_iff, hiff])

/-- Central differences make the displacement at one vector a homomorphism. -/
def centralDifferenceHom (ρ : SL →* MulAut E) (K : Subgroup SL) (w : E)
    (hcentral : ∀ k ∈ K, ∀ g : SL, ρ g (w⁻¹ * ρ k w) = w⁻¹ * ρ k w) : K →* E where
  toFun k := w⁻¹ * ρ k w
  map_one' := by simp
  map_mul' k l := by
    have h := hcentral l l.property k
    simp only [map_mul, map_inv] at h
    change w⁻¹ * ρ ((k : SL) * l) w = (w⁻¹ * ρ k w) * (w⁻¹ * ρ l w)
    rw [map_mul, MulAut.mul_apply]
    calc
      _ = (w⁻¹ * ρ k w) * ((ρ k w)⁻¹ * ρ k (ρ l w)) := by group
      _ = _ := by rw [h]

/-- An element of order dividing three cannot move a vector by a fixed binary difference. -/
theorem fixed_of_cube_of_fixed_difference (ρ : SL →* MulAut E) (k : SL) (w : E)
    (hcube : k ^ 3 = 1) (hcentral : ρ k (w⁻¹ * ρ k w) = w⁻¹ * ρ k w) :
    ρ k w = w := by
  let z := w⁻¹ * ρ k w
  have hz : ρ k z = z := hcentral
  have he : ρ k w = w * z := by simp [z]
  have hs : z ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 E) z
  have hpow (n : ℕ) : ρ (k ^ n) w = w * z ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', map_mul, MulAut.mul_apply, ih, map_mul, map_pow, he, hz, pow_succ']
      exact mul_assoc _ _ _
  have h3 := hpow 3
  rw [hcube, map_one, MulAut.one_apply, pow_succ, hs, one_mul] at h3
  have hz1 : z = 1 := mul_left_cancel (h3.symm.trans (mul_one w).symm)
  simpa only [hz1, mul_one] using he

/-- The original escaping configuration supplies globally fixed stabilizer differences. -/
theorem seed_difference_fixed [Finite E] (ρ : SL →* MulAut E)
    (d : EscapingConfiguration ρ) (hline : (actionOrbitCore ρ d.seed).relIndex d.seed = 2)
    (w : E) (hw : w ∈ d.seed) (k : SL)
    (hk : k ∈ markedPointStabilizer d.marking d.point) (g : SL) :
    ρ g (w⁻¹ * ρ k w) = w⁻¹ * ρ k w :=
  orbitCore_fixed_of_index_two ρ d hline g _ (seed_difference_mem_core ρ d hline k hk w hw)

/-- The cubic part of the marked stabilizer already fixes the seed pointwise. -/
theorem seed_fixed_of_cube [Finite E] (ρ : SL →* MulAut E)
    (d : EscapingConfiguration ρ) (hline : (actionOrbitCore ρ d.seed).relIndex d.seed = 2)
    (k : SL) (hk : k ∈ markedPointStabilizer d.marking d.point) (hcube : k ^ 3 = 1)
    (w : E) (hw : w ∈ d.seed) : ρ k w = w :=
  fixed_of_cube_of_fixed_difference ρ k w hcube (seed_difference_fixed ρ d hline w hw k hk k)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
