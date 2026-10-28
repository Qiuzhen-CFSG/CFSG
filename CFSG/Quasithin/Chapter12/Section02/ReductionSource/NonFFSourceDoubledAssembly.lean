module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubled
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledFF

/-!
# Doubled-row assembly after the binary natural FF exclusion

The original chosen seed and conjugator now supply the binary four- and
five-space FF argument. This removes that callback from the earlier
assembly while preserving its public interface. The other four source
arguments remain explicit: nonbinary linear bounds, binary SL₃ centralizer
geometry, paired symplectic bounds including A₆, and the improved A₇ bound.

This is a conditional reduction of the remaining non-FF cases, not their
completed exclusion. Source: Aschbacher--Smith 7.1--7.7 and 12.2.2,
printed pp.696--709 and 795.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Doubled-row assembly with the binary natural four- and five-space FF
argument discharged on the original orbit. The nonbinary linear, binary
centralizer, symplectic (including A₆), and A₇ bounds remain explicit. -/
theorem sourceOrbit_false_of_markedDoubled_bounds
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : D.MarkedDoubled)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hlinear : ∀ F : BinaryField, 1 < F.degree →
      Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
        (linearNatural F 3)) → DoubledLinearBounds D.sourceOrbit T F.degree)
    (hbinary : ∀ F : BinaryField, F.degree = 1 →
      Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
        (linearNatural F 3)) → DoubledBinaryGeometry D.sourceOrbit)
    (hsymplectic : ∀ F : BinaryField, 1 < F.degree →
      Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
        (Representation.restrictScalars (k := ZMod 2)
          (symplecticNatural (k := F.Carrier) 2))) →
        DoubledSymplecticBounds D.sourceOrbit T F.degree)
    (hsix : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)) → DoubledSymplecticBounds D.sourceOrbit T 1)
    (hseven : ∀ σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2),
      Function.Injective σ →
      Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ) →
      DoubledSevenBounds D.sourceOrbit T) : False :=
  D.sourceOrbit_false_of_markedDoubled_inputs h hd hnon hlinear hbinary hsymplectic hsix
    (fun _ hn hm => D.sourceOrbit_isFF_of_markedDoubled_binaryNatural h hd hn hm) hseven

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
