module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.NaturalBlocks
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.CubicKernel
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.Source

/-!
# Normal-branch assembly with the local kernel restrictions discharged

Every escaping χ₀ block now has a three-prime intersection with M.
A natural block's full Borel cannot lie in M, since the constructed odd
actor would centralize W and force the block back into M. These proved
restrictions feed the existing point-centralizer and degree-five closure
consumer on the literal original subgroups.

This remains a conditional source assembly: component exclusion, the
remaining block-placement and cubic-block arguments, and the nonnormal
parabolic argument still belong to qt-d-double-natural-centralizers.
The final pure-fusion and weak-closure discharge remains at
qt-d-1222-double-natural. No source obligation is removed by this reduction.
Source: Aschbacher--Smith, 12.1.1--3, printed pp.788--790.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement IsMulCommutative
open BinaryLinear.OuterCyclic BinaryNaturalDual.ModelOrbits.AutomorphismModel
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter4 ChapterC ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
/-- The actual centralizer and degree-five closure consumer with both local block restrictions discharged. -/
theorem doubleNatural_nonsingular_controls_of_normal_local_obstructions_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w)) →
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ∀ K : Subgroup G,
        K ≤ sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w) →
        IsChiZeroBlockIn (K.subgroupOf
          (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w))) →
        IsChiZeroBlockIn (K.subgroupOf (B.pointCentralizer w)) →
        K = ⁅K,elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2)⁆ →
        (∀ N : Subgroup G, N ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
          (N.subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ (K ⊔ B.pointSylow w))).Normal → N = ⊥) →
        Nat.Coprime 3 (Nat.card (K ⊓ normalizer (L : Set G) : Subgroup G)) →
        (∀ k, IsL2EvenBlock K k → ∀ P : Sylow 2 K,
          ¬ (normalizer (P : Set K)).map K.subtype ≤ normalizer (L : Set G)) →
        K ≤ normalizer (L : Set G)) →
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
      B.pointResidual w ≤ centralizer (B.fixedLine : Set G)) →
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < globalW (componentOrbit V (T : Subgroup G)) T) := by
  let := D.doubledOrbit_elementary h
  intro hchar hblocks hparabolic
  apply D.doubleNatural_nonsingular_controls_of_normal_blocks_of_many h hmany B hchar _ hparabolic
  intro S w hw hc hn K hKY hKYblock hKHblock hmove hno
  by_cases hKM : K ≤ normalizer (L : Set G)
  · exact hKM
  apply hblocks S w hw hc hn K hKY hKYblock hKHblock hmove hno
  · apply (D.doubleNatural_local_sectionCentralizer_three_prime h B S w hw.nonsingular).coprime_dvd_right
    apply card_dvd_of_le
    intro x hx
    exact ⟨⟨hx.2,(hKY hx.1).1⟩,(hKY hx.1).2⟩
  · intro k hnat P hPM
    exact hKM (D.doubleNatural_normal_natural_block_le_of_borel h B S w hw hc hn K hKY hKYblock.1 k hnat P hPM)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
