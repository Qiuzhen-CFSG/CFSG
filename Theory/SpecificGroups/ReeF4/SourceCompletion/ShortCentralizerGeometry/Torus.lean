module
public import Theory.SpecificGroups.ReeF4.SourceCompletion.ShortCentralizerGeometry.Plane
public import Theory.SpecificGroups.ReeF4.SourceCompletion.CartanNormalizer
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# The full linear parabolic preserves the long-root plane

The complete fixed torus preserves the central long-root line and its Weyl
conjugate, hence their two-dimensional plane. Together with the unipotent and
Weyl calculations this proves normalization by the full linear parabolic,
including its complementary torus.

Source: the natural-module step of Aschbacher--Smith F.4.42, printed p.295
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace ReeF4.SourceCompletion.ShortCentralizerGeometry
open Parabolics LargeLocalSeeds EvenInvolutionGeometry ElementaryTwoBound
open Parabolics.Binary.FixedGeometry
open ElementaryTwoBound.Replacement ElementaryTwoBound.Replacement.CentralizerGeometry
open NormalizedRootCentralizers.CenterExponent
open SectionGeometry.BNPair

private theorem torus_normalizes_long (m : ℕ) (hm : 0 < m) :
    fixedTorus m ≤ normalizer (longRootGroup m : Set (Model m)) := by
  rw [←unipotent_center_eq_longRootGroup m hm]
  exact ((fixedTorus_le_borel m).trans (borel_le_unipotent_normalizer m)).trans
    (normalizer_le_normalizer_characteristic_image (unipotent m) (center (unipotent m)))

private theorem weyl_long_mem_plane (m : ℕ) (a : CoefficientField m) :
    weylLift m .linear * longRootElement m a * (weylLift m .linear)⁻¹ =
      centralElement m 2 a := by
  have h := weyl_conjugate_plane m 0 a
  have heq : longRootElement m a = centralElement m 4 a := by
    apply Subtype.ext
    rfl
  rw [heq]
  simpa only [centralElement_zero,mul_one,one_mul] using h

/-- The entire fixed torus preserves the plane, not only the PSL₂ torus. -/
theorem torus_normalizes_plane (m : ℕ) (hm : 0 < m) :
    fixedTorus m ≤ normalizer (Replacement.V m : Set (Model m)) := by
  rw [le_normalizer_iff]
  intro z hz v hv
  obtain ⟨a,b,rfl⟩ := (mem_V_iff m v).mp hv
  have hN := (normalizer_fixedTorus_eq_words hm).symm.le
    (weylLift_mem_normalizerWords m .linear)
  have hwz : (weylLift m .linear)⁻¹ * z * weylLift m .linear ∈ fixedTorus m := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp (inv_mem hN) z).mp hz
  have h4 : z * longRootElement m b * z⁻¹ ∈ longRootGroup m :=
    (mem_normalizer_iff.mp (torus_normalizes_long m hm hz) _).mp
      ((mem_longRootGroup m _).mpr ⟨b,rfl⟩)
  obtain ⟨b',hb'⟩ := (mem_longRootGroup m _).mp h4
  have h2 : ((weylLift m .linear)⁻¹ * z * weylLift m .linear) *
      longRootElement m a * ((weylLift m .linear)⁻¹ * z * weylLift m .linear)⁻¹ ∈
      longRootGroup m :=
    (mem_normalizer_iff.mp (torus_normalizes_long m hm hwz) _).mp
      ((mem_longRootGroup m _).mpr ⟨a,rfl⟩)
  obtain ⟨a',ha'⟩ := (mem_longRootGroup m _).mp h2
  have h2' : z * centralElement m 2 a * z⁻¹ = centralElement m 2 a' := by
    rw [←weyl_long_mem_plane m a,←weyl_long_mem_plane m a']
    rw [ha']
    group
  have h4' : z * centralElement m 4 b * z⁻¹ = centralElement m 4 b' := hb'.symm
  have he : z * (centralElement m 4 b * centralElement m 2 a) * z⁻¹ =
      centralElement m 4 b' * centralElement m 2 a' := by
    rw [←h4',←h2']; group
  rw [he]
  exact (mem_V_iff m _).mpr ⟨a',b',rfl⟩

/-- The full linear parabolic normalizes the long-root plane. -/
theorem parabolic_normalizes_plane (m : ℕ) (hm : 0 < m) :
    parabolic m .linear ≤ normalizer (Replacement.V m : Set (Model m)) := by
  rw [SectionGeometry.BNPair.parabolic_eq_seed_sup_borel m .linear,
    SectionGeometry.BNPair.borel_eq_unipotent_sup_fixedTorus]
  exact sup_le (seed_normalizes_plane m hm)
    (sup_le (unipotent_normalizes_plane m) (torus_normalizes_plane m hm))

end ReeF4.SourceCompletion.ShortCentralizerGeometry
