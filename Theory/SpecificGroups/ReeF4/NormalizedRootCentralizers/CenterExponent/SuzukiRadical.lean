module
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter.TailIdentification
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks.QuartetSplitting.EightAmbient
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore
-- Internal extension of the coordinate calculation; only proof terms use
-- its private eliminations and the concrete root-layout implementation.
import all Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.MiddleElimination
import all Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter.TailIdentification
import all Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.FixedRootFactorization.RootAlignment

/-!
# The center of the Suzuki-side Ree radical

Commutation with the seven radical root curves eliminates every positive
coordinate except the central fifth parameter. This remaining root curve
centralizes the whole Suzuki seed. Thus the centralizer of the seed's
two-core lies in its center, on the original fixed matrix carrier.
The internal imports extend the existing coordinate calculation without
exposing its private eliminations in the public mathematical statements.

Source: Aschbacher--Smith 4.4.12 and F.1.12(I)(5), printed pp.621--622
and 263--264; GLS3 2.4.5(d), 2.4.6 and Table 2.4.
-/

public noncomputable section
open Subgroup
namespace ReeF4.NormalizedRootCentralizers.CenterExponent
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates LargeLocalSeeds
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators OuterElimination
open EvenInvolutionGeometry.UnipotentCenter

/-- The seven radical curves already detect all but the central fifth parameter. -/
theorem positiveWord_eq_central_fifth_of_radical_commute (m : ℕ) (p : PositiveParameters m)
    (hcomm : ∀ i : Fin 8, i ≠ 0 → ∀ t : CoefficientField m,
      Commute (positiveWord m p) (rootWord m i t)) :
    positiveWord m p = centralWord m 4 (p.central 1) := by
  let v := parameters m p
  have h (i : Fin 8) (hi : i ≠ 0) : Commute (splitWord m v) (rootWord m i 1) := by
    rw [← positiveWord_split]
    exact hcomm i hi 1
  obtain ⟨h0,h18⟩ := detect_fourth m v (h 3 (by decide))
  have hm0 : p.main 0 = 0 := h0
  have hm2 : p.main 2 = 0 := h18
  have h1 : v 1 = 0 := by change halfFrobenius m (p.main 0) = 0; rw [hm0,map_zero]
  have h19 : v 19 = 0 := by change halfFrobenius m (p.main 2) = 0; rw [hm2,map_zero]
  have h22 := detect_second m v h0 h1 h18 h19 (h 1 (by decide))
  have hp0 : p.pair 0 = 0 := h22
  have h23 : v 23 = 0 := by change halfFrobenius m (p.pair 0) = 0; rw [hp0,map_zero]
  obtain ⟨hp1,hc0⟩ := detect_seventh m v h0 h1 h18 h19 h22 h23 (h 6 (by decide))
  have ho : OuterCoordinatesZero p := ⟨hp0,hp1,hm0,hm2,hc0⟩
  have hm3 := MiddleElimination.main_third_zero m p ho (hcomm 4 (by decide) 1)
  have hm1 := MiddleElimination.main_fifth_zero m p ho hm3 (hcomm 2 (by decide) 1)
  have hc (i : Fin 8) (hi : i ≠ 0) :
      Commute (tailSplitWord m (parameters m p)) (rootWord m i 1) := by
    rw [← positiveWord_tail m p ho hm1 hm3]
    exact hcomm i hi 1
  have hp2 : p.pair 2 = 0 := detect_pairsixth m _ (hc 2 (by decide))
  have hp3 : p.pair 3 = 0 := detect_pairfourth m _ (hc 6 (by decide))
  have hc2 : p.central 2 = 0 := detect_centralseventh m _ (hc 1 (by decide))
  have hc3 : p.central 3 = 0 := detect_centralthird m _ (hc 7 (by decide))
  simp [positiveWord, positive_pair_indices, positive_quartet_indices,
    pairCount, quartetCount, List.ofFn_succ, ho.pair_eighth, ho.pair_second,
    ho.main_first, ho.main_seventh, ho.central_first, hm1, hm3, hp2, hp3, hc2, hc3]

private theorem suzuki_radical_covers (i : Fin 8) (hi : i ≠ 0) :
    (∃ j, radicalRootWordLayout.pairIndex j = i) ∨
      (∃ j, radicalRootWordLayout.quartetIndex j = i) := by
  fin_cases i
  · exact (hi rfl).elim
  · exact Or.inl ⟨⟨1,by decide⟩,rfl⟩
  · exact Or.inr ⟨⟨2,by decide⟩,rfl⟩
  · exact Or.inl ⟨⟨3,by decide⟩,rfl⟩
  · exact Or.inr ⟨⟨0,by decide⟩,rfl⟩
  · exact Or.inl ⟨⟨2,by decide⟩,rfl⟩
  · exact Or.inr ⟨⟨1,by decide⟩,rfl⟩
  · exact Or.inl ⟨⟨0,by decide⟩,rfl⟩

theorem mainElement_mem_suzuki_radical (m : ℕ) (i : Fin 8) (hi : i ≠ 0)
    (t : CoefficientField m) : mainElement m i t ∈ radical m .suzuki := by
  change toSplitGroup m (mainElement m i t) ∈ splitRadical m .suzuki
  rw [mainElement_coe]
  rcases suzuki_radical_covers i hi with ⟨j,rfl⟩ | ⟨j,rfl⟩
  · exact (radicalRootWordLayout.pair_root_fixed_mem m (mixedRootCommutation m) j t).2
  · exact (radicalRootWordLayout.quartet_root_fixed_mem m (mixedRootCommutation m)
      (b2RootSwap m) j t).2

/-- The center of the Suzuki radical centralizes its whole perfect seed. -/
theorem suzuki_radical_center_centralizes_seed (m : ℕ) (x : Model m)
    (hx : x ∈ radical m .suzuki)
    (hc : ∀ y ∈ radical m .suzuki, Commute x y) :
    ∀ y ∈ seed m .suzuki, Commute x y := by
  have hxU : x ∈ unipotent m := splitRadical_le_unipotent m .suzuki hx
  obtain ⟨p,hp⟩ := exists_positiveWord m x hxU
  have hword : toSplitGroup m x = centralWord m 4 (p.central 1) := hp.trans
    (positiveWord_eq_central_fifth_of_radical_commute m p (by
      intro i hi t
      have hh := (hc _ (mainElement_mem_suzuki_radical m i hi t)).map (toSplitGroup m)
      rwa [hp, mainElement_coe] at hh))
  have he : x = ElementaryTwoBound.centralElement m 4 (p.central 1) := by
    apply toSplitGroup_injective m
    rw [ElementaryTwoBound.centralElement_coe]
    exact hword
  rw [he]
  exact CentralCovers.TwoPrimary.QuartetSplitting.EightAmbient.central_fifth_commute_seed m _

/-- In the actual canonical seed, the centralizer of its two-core is central. -/
theorem suzuki_seed_core_centralizer_le_center {m : ℕ} (hm : 1 ≤ m) :
    centralizer (pCore 2 (standardSeed (canonicalLocalBlockInput m) .suzuki) :
      Set (standardSeed (canonicalLocalBlockInput m) .suzuki)) ≤
      center (standardSeed (canonicalLocalBlockInput m) .suzuki) := by
  let d := canonicalLocalBlockInput m
  rw [← suzuki_seedRadical_eq_pCore hm d]
  intro x hx
  have hxR := LargeLocalSeeds.suzuki_seedRadical_centralizer_le hm d hx
  let a := seedEquiv m .suzuki
  have hxR' : (a x : Model m) ∈ radical m .suzuki := by
    change toSplitGroup m (a x) ∈ splitRadical m .suzuki
    rw [seedEquiv_coe]
    exact hxR
  have hc : ∀ y ∈ radical m .suzuki, Commute (a x : Model m) y := by
    intro y hy
    have hyS : y ∈ seed m .suzuki := (radical_le_unipotent m .suzuki).trans (unipotent_le_seed m .suzuki) hy
    let b := a.symm ⟨y,hyS⟩
    have hb : b ∈ seedRadical d .suzuki := by
      change b.val.val ∈ splitRadical m .suzuki
      rw [← seedEquiv_coe m .suzuki b]
      change toSplitGroup m (a (a.symm ⟨y,hyS⟩)) ∈ splitRadical m .suzuki
      rw [a.apply_symm_apply]
      exact hy
    have hh := (show Commute x b from (mem_centralizer_iff.mp hx b hb).symm).map a.toMonoidHom
    have hh' := hh.map (seed m .suzuki).subtype
    change Commute (a x : Model m) (a b : Model m) at hh'
    dsimp only [b] at hh'
    rw [a.apply_symm_apply] at hh'
    exact hh'
  apply mem_center_iff.mpr
  intro y
  apply a.injective
  apply Subtype.ext
  simp only [map_mul, Subgroup.coe_mul]
  exact (suzuki_radical_center_centralizes_seed m _ hxR' hc (a y) (a y).property).eq.symm
end ReeF4.NormalizedRootCentralizers.CenterExponent
