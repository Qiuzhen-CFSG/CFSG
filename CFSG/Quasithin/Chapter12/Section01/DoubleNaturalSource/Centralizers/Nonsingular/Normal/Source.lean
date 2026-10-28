module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.Blocks
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Assembly
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Assembly

/-!
# Applying the normal-residual block reduction to the doubled orbit

Construct the compatible H.9 source model and reduce the normal-residual
branch of 12.1.1 to its actual outside χ₀ blocks. The factorization, Sylow
promotion, characteristic-two descent, relative block transport, Thompson
movement and common-normal exclusion are all supplied by the preceding
modules. The resulting nonsingular conclusion feeds 12.1.2 and the proved
degree-five zeroth-closure argument in the original source order.

This assembly remains conditional on characteristic two, the exclusion of
the specified blocks, and the nonnormal parabolic argument. These source
obligations belong to qt-d-double-natural-centralizers; final assembly is
owned by qt-d-1222-double-natural. No pure fusion or degree-four closure
is used in the degree-five implication.
Source: Aschbacher--Smith, 12.1.1--3, printed pp.788--789.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter4 ChapterC ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal chosen-module consumer of the normal-residual block reduction.
The model and degree-five action inputs are proved; the three remaining
ambient source arguments are displayed explicitly. -/
theorem doubleNatural_nonsingular_controls_of_normal_blocks_of_many
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
  obtain ⟨S⟩ := D.doubleNatural_sourceModel_of_many h hmany B
  have hc : B.NonsingularCentralizers := by
    apply D.doubleNatural_nonsingularCentralizers_of_branches h B S (hchar S) _ (hparabolic S)
    intro w hw hc hn
    by_contra hout
    obtain ⟨K,hKY,hKYblock,hKHblock,hKM,hmove,hno⟩ :=
      D.doubleNatural_adapted_normal_outside_chiZero h B S w hw hc hn hout
    exact hKM (hblocks S w hw hc hn K hKY hKYblock hKHblock hmove hno)
  refine ⟨hc,B.globalR_ge (D.doubledOrbit_normalizer_eq h B.orbit_eq) hc,?_⟩
  intro hn
  subst n
  exact (D.doubledFive_zeroClosure_of_nonsingular_of_many h hmany B hc).2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
