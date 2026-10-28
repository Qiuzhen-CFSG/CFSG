module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Adapted
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Core

/-!
# Assembly of the three ambient branches in 12.1.1

The characteristic-two reduction, normal-residual block argument and
nonnormal parabolic argument are explicit, independent source premises.
The last branch must produce centralization of the original T-fixed line;
the actual residual mover supplied by the corrected H.9 marking contradicts
it. Conjugation then covers every nonsingular point, and the quadratic
geometry gives the 12.1.2 global r-bound on the original doubled orbit.

This is conditional assembly, not a proof of the missing ambient branches.
Source: Aschbacher--Smith 12.1.1--2, printed pp.788--789.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The three genuine source branches suffice, with no ambient normality
substituted for normality of the residual inside its point centralizer. -/
theorem doubleNatural_nonsingularCentralizers_of_branches
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel,
      (∀ w, B.AdaptedPoint S w →
        generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w)) →
      (∀ w, B.AdaptedPoint S w →
        generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
        ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
        B.pointCentralizer w ≤ normalizer (L : Set G)) →
      (∀ w, B.AdaptedPoint S w →
        generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
        ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
        ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
        B.pointResidual w ≤ centralizer (B.fixedLine : Set G)) →
      B.NonsingularCentralizers := by
  let := D.doubledOrbit_elementary h
  intro S hchar hnormal hparabolic
  apply D.doubleNatural_nonsingularCentralizers_of_adapted h B S
  intro w hw
  have hc := hchar w hw
  by_cases hn : ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal
  · exact hnormal w hw hc hn
  · by_contra hout
    exact hw.residual_moves (hparabolic w hw hc hn hout)

/-- The literal 12.1.2(2) consumer, retaining exactly the same three earlier
source obligations as the point-centralizer assembly. -/
theorem doubleNatural_globalR_ge_of_nonsingular_branches
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel,
      (∀ w, B.AdaptedPoint S w →
        generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w)) →
      (∀ w, B.AdaptedPoint S w →
        generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
        ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
        B.pointCentralizer w ≤ normalizer (L : Set G)) →
      (∀ w, B.AdaptedPoint S w →
        generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
        ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
        ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
        B.pointResidual w ≤ centralizer (B.fixedLine : Set G)) →
      (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) := by
  let := D.doubledOrbit_elementary h
  intro S hchar hnormal hparabolic
  exact B.globalR_ge (D.doubledOrbit_normalizer_eq h B.orbit_eq)
    (D.doubleNatural_nonsingularCentralizers_of_branches h B S hchar hnormal hparabolic)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
