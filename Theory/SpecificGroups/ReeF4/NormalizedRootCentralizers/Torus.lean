module

public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.Roots
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.CorootRealization
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.FixedProducts

/-!
# Diagonal rigidity of the concrete Ree long-root curve

The source long-root curve y₅(t) is the product of the high and mixed split
roots in the fifth relative block. Unique positive block coordinates detect
its two parameters independently. Direct diagonal conjugation scales each
parameter by the corresponding inverse torus character. Fixing a nonzero
parameter forces both characters to be one, so every parameter is fixed.

The resulting uniform centralizer equality is for the genuine fixed coroot
torus in Model m. Identifying this curve with the whole unipotent center is
a separate calculation. No Sylow-center identification or global involution
centralizer classification is assumed or asserted here.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927; GLS3 Table 2.4 and
2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`. The matrix and root conventions
are those of `EvenInvolutionGeometry/Roots.lean`.
-/

public section
noncomputable section
namespace ReeF4.NormalizedRootCentralizers
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics LargeLocalSeeds EvenInvolutionGeometry
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics.RadicalCoordinates.FixedCoordinates
open Subgroup

private theorem root_zero (m : ℕ) (r : F4Chevalley.Root) :
    rootGeneratorInGroup m r 0 = 1 := Subtype.ext (F4Chevalley.rootCurve_zero r)

private theorem exists_quartet_four :
    ∃ j, positiveRootWordLayout.quartetIndex j = 4 := by
  rcases positiveRootWordLayout.positive_covers 4 with ⟨j, hj⟩ | h
  · have hp := positiveRootWordLayout.pair_odd j
    rw [hj] at hp
    exact (hp (by decide)).elim
  · exact h

private def topParameters (m : ℕ) (j : Fin (quartetCount .positive))
    (a b : CoefficientField m) : BlockParameters m .positive :=
  (fun _ _ => 0, fun i => if i = j then ![0, 0, b, a] else (fun _ => 0))

private theorem top_blockWord (B : RootBlocks .positive) (m : ℕ)
    (j : Fin (quartetCount .positive)) (a b : CoefficientField m) :
    B.blockWord m (topParameters m j a b) =
      rootGeneratorInGroup m (B.roots (.inr (j, 2))).val b *
        rootGeneratorInGroup m (B.roots (.inr (j, 3))).val a := by
  fin_cases j <;>
    simp [RootBlocks.blockWord, topParameters, pairCount, quartetCount, List.ofFn_succ,
      pairWord, quartetWord, root_zero]

/-- The two top coordinates in the fifth relative block are independent. -/
theorem top_roots_injective (m : ℕ) (a b c d : CoefficientField m)
    (h : rootGeneratorInGroup m (highRoot 4) a * rootGeneratorInGroup m (mixedRoot 4) b =
      rootGeneratorInGroup m (highRoot 4) c * rootGeneratorInGroup m (mixedRoot 4) d) :
    a = c ∧ b = d := by
  obtain ⟨j, hj⟩ := exists_quartet_four
  have hw (x y : CoefficientField m) :
      positiveRootWordLayout.blocks.blockWord m (topParameters m j x y) =
      rootGeneratorInGroup m (highRoot 4) x * rootGeneratorInGroup m (mixedRoot 4) y := by
    rw [top_blockWord, positiveRootWordLayout.quartet_mixed,
      positiveRootWordLayout.quartet_high]
    exact (positiveRootWordLayout.quartet_top_commute m (mixedRootCommutation m) j x y).eq.symm.trans
      (by rw [hj])
  rw [← hw, ← hw] at h
  have hp := positiveRootWordLayout.blocks.blockWord_injective m
    (RadicalCoordinates.wordInSubgroup_bijective m _) h
  constructor
  · simpa [topParameters] using
      congrArg (fun p : BlockParameters m .positive => p.2 j 3) hp
  · simpa [topParameters] using
      congrArg (fun p : BlockParameters m .positive => p.2 j 2) hp

private def scale (m : ℕ) (u : TorusParameter m) (r : F4Chevalley.Root) :
    CoefficientField m :=
  (RootPairing.IntegralGeckConstruction.integralChevalleyRootScale
    (P := typeF4RootPairing) u⁻¹ r : (CoefficientField m)ˣ)

private theorem diagonal_conj_root (m : ℕ) (u : TorusParameter m)
    (z : SplitGroup m) (hz : z.val = diagonalTorusHom m u)
    (r : F4Chevalley.Root) (a : CoefficientField m) :
    z * rootGeneratorInGroup m r a * z⁻¹ =
      rootGeneratorInGroup m r (scale m u r * a) := by
  apply Subtype.ext
  change z.val * F4Chevalley.rootCurve r a * z.val⁻¹ = _
  rw [hz]
  have he := F4Chevalley.rootCurve_torus_conjugation u⁻¹ r a
  simpa only [← diagonalTorusHom_apply, map_inv, inv_inv, rootGeneratorInGroup_coe, scale] using he

/-- A diagonal matrix fixing a nonzero fifth-block central word fixes every
parameter on that curve. Both split root coordinates are detected separately. -/
theorem diagonal_centralizes_longRoot (m : ℕ) (z : SplitGroup m)
    (hz : z ∈ diagonalTorus m) (a : CoefficientField m) (ha : a ≠ 0)
    (hc : Commute z (centralWord m 4 a)) (b : CoefficientField m) :
    Commute z (centralWord m 4 b) := by
  obtain ⟨u, hu⟩ := hz
  have hconj (t : CoefficientField m) :
      z * centralWord m 4 t * z⁻¹ =
      rootGeneratorInGroup m (highRoot 4) (scale m u (highRoot 4) * t) *
        rootGeneratorInGroup m (mixedRoot 4)
          (scale m u (mixedRoot 4) * rootFieldEnd m (longRoot 4) t) := by
    calc
      _ = (z * rootGeneratorInGroup m (highRoot 4) t * z⁻¹) *
          (z * rootGeneratorInGroup m (mixedRoot 4) (rootFieldEnd m (longRoot 4) t) * z⁻¹) := by
        simp only [centralWord]
        group
      _ = _ := by rw [diagonal_conj_root m u z hu.symm, diagonal_conj_root m u z hu.symm]
  have he : z * centralWord m 4 a * z⁻¹ = centralWord m 4 a := by
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [hconj] at he
  have hs := top_roots_injective m _ _ _ _ he
  have hfa : rootFieldEnd m (longRoot 4) a ≠ 0 := by
    simpa using ha
  have hs₁ : scale m u (highRoot 4) = 1 :=
    mul_right_cancel₀ ha (hs.1.trans (one_mul a).symm)
  have hs₂ : scale m u (mixedRoot 4) = 1 :=
    mul_right_cancel₀ hfa (hs.2.trans (one_mul _).symm)
  have hb : z * centralWord m 4 b * z⁻¹ = centralWord m 4 b := by
    rw [hconj, hs₁, hs₂, one_mul, one_mul]
    rfl
  exact (mul_inv_eq_iff_eq_mul.mp hb : _)

/-- Uniform centralizers in the genuine fixed coroot torus. -/
theorem fixedTorus_centralizers (m : ℕ) (r : Model m)
    (hr : r ∈ longRootGroup m) (hne : r ≠ 1) :
    fixedTorus m ⊓ centralizer ({r} : Set (Model m)) =
      fixedTorus m ⊓ centralizer (longRootGroup m : Set (Model m)) := by
  obtain ⟨a, rfl⟩ := (mem_longRootGroup m r).mp hr
  have ha : a ≠ 0 := by simpa using hne
  apply le_antisymm
  · intro z hz
    have hzt : toSplitGroup m z ∈ splitTorus m := hz.1
    rw [splitTorus_eq_diagonalTorus m] at hzt
    refine ⟨hz.1, mem_centralizer_iff.mpr ?_⟩
    intro x hx
    obtain ⟨b, rfl⟩ := (mem_longRootGroup m x).mp hx
    apply toSplitGroup_injective m
    simpa only [map_mul, longRootElement_coe] using
      (diagonal_centralizes_longRoot m (toSplitGroup m z)
        hzt
        a ha
        (by simpa only [longRootElement_coe] using
          (show Commute z (longRootElement m a) from mem_centralizer_singleton_iff.mp hz.2).map (toSplitGroup m)) b).eq.symm
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr
      ((mem_longRootGroup m _).mpr ⟨a, rfl⟩)))

end ReeF4.NormalizedRootCentralizers
