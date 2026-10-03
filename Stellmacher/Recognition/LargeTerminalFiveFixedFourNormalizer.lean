module

public import Stellmacher.Recognition.LargeTerminalInvolutionCentralizerQuotient
public import Stellmacher.Recognition.LargeTerminalDerivedCentralizer
public import Stellmacher.Recognition.LargeTerminalDerivedCentralizerNormalizer
public import Stellmacher.Recognition.LargeTerminalFiveFixedFourCentralizerCore
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Confinement of the actual fixed-four normalizer

Write Q for the second core, R for the first residual, and V = C_Q(A).
The distinguished involution belongs to V, so C_G(V) lies in the second
local group. Every element of N_G(V) normalizes O₂(C_G(V)). This reduces
normalizer confinement to identifying that characteristic core and
controlling its normalizer.

The centralizer-core theorem identifies O₂(C_G(V)) with W = C_Q(R'),
whose order is 64. The derived-centralizer normalizer theorem confines
N_G(W) to the second local group. Composing these results proves the
unconditional confinement of N_G(V). In particular, no maximality of the
second local group is needed.

Source: Thompson VI, printed p.630, the normalizer assertion in the
noncyclic four-fixed alternative. These reductions use only two-local
information and do not assert invariance under the full five-centralizer.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix Subgroup

universe u

/-- The centralizer of the actual fixed four-group is confined by its
distinguished involution. -/
public theorem LargeTerminalContext.five_fixed_four_centralizer_le_second
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    centralizer (twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Set G) ≤
      ctx.second := by
  obtain ⟨_, hZV, _⟩ := ctx.five_fixed_four_ambient_data A hAN hcard hncyc hfixed
  obtain ⟨z, hz, hgen, _⟩ := ctx.involution_centralizer_core
  have hzV : z ∈ twoCoreIn ctx.second ⊓ centralizer (A : Set G) :=
    hZV (hgen ▸ mem_zpowers z)
  exact (centralizer_le (Set.singleton_subset_iff.mpr hzV)).trans_eq
    (ctx.involution_centralizer_eq_second hS z hz hgen)

/-- The normalizer of the actual fixed group preserves the two-core of
its full centralizer, without assuming invariance under C_G(A). -/
public theorem LargeTerminalContext.five_fixed_four_normalizer_le_core_normalizer
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) :
    let V := twoCoreIn ctx.second ⊓ centralizer (A : Set G)
    normalizer (V : Set G) ≤
      normalizer (twoCoreIn (centralizer (V : Set G)) : Set G) := by
  let V := twoCoreIn ctx.second ⊓ centralizer (A : Set G)
  exact (normalizer_le_normalizer_centralizer V).trans
    (normalizer_le_normalizer_characteristic_image
      (centralizer (V : Set G)) (pCore 2 (centralizer (V : Set G))))

/-- Identification of the centralizer core and control of the derived
centralizer's normalizer finish confinement of the actual fixed-four normalizer. -/
public theorem LargeTerminalContext.five_fixed_four_normalizer_le_of_core_control
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G)
    (hcore : twoCoreIn (centralizer
      (twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Set G)) =
        twoCoreIn ctx.second ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G))
    (hNW : normalizer
      (twoCoreIn ctx.second ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G) : Set G) ≤
        ctx.second) :
    normalizer (twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Set G) ≤
      ctx.second := by
  have h := ctx.five_fixed_four_normalizer_le_core_normalizer A
  dsimp only at h
  change twoCoreIn (centralizer
    ((twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Subgroup G) : Set G)) = _ at hcore
  rw [hcore] at h
  exact h.trans hNW

/-- The full normalizer of the actual noncyclic fixed four-group lies in
the second local group. Its action preserves the two-core of the full
centralizer, which is the confined derived centralizer. -/
public theorem LargeTerminalContext.five_fixed_four_normalizer_le_second
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    normalizer (twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Set G) ≤
      ctx.second := by
  exact ctx.five_fixed_four_normalizer_le_of_core_control A
    (ctx.five_fixed_four_centralizer_core_eq hS A hA hAP hAN hcard hncyc hfixed)
    (ctx.derived_centralizer_normalizer_le_second hS)

end Stellmacher.Recognition
