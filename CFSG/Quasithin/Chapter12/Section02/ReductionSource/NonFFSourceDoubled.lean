module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSetup
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBounds

/-!
# Conditional assembly of the marked non-FF doubled rows

The actual marked constituent disjunction reduces to five independent
source arguments: nonbinary natural/dual SL3 bounds, binary SL3 centralizer
geometry, paired symplectic bounds (including A6), the A7 improved bound,
and FF for the binary natural four- and five-space pairs. The last input
is representation-theoretic; this file does not repeat the ambient
12.1.11 doubled-natural exclusion.

Every numerical or geometry input is explicit. Their construction under
the original multiple-overgroup hypothesis remains with the row producers;
this conditional theorem is not the completed doubled-branch exclusion.
Source: Aschbacher--Smith D.3.10, 7.1.1, 7.3.5, 7.5.2, 7.5.5 and7.6.1,
printed pp.201 and696--703, applied in12.2.2, p.795.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual chosen-module application of all doubled-row terminal
arguments. The displayed row inputs have not been discharged here. -/
theorem sourceOrbit_false_of_markedDoubled_inputs
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
    (hff : ∀ n : ℕ, (n = 4 ∨ n = 5) →
      Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
        (linearNatural BinaryField.two n)) → IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hseven : ∀ σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2),
      Function.Injective σ →
      Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ) →
      DoubledSevenBounds D.sourceOrbit T) : False := by
  have hT := D.sourceOrbit_weakClosure_setup
  have hFF := D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon
  rcases hd.2.1 with ⟨F,hF⟩ | ⟨F,hn,hF⟩ | hF | ⟨n,hn,hF⟩ | ⟨σ,hσ,hF⟩
  · by_cases hn : F.degree = 1
    · exact DoubledBinaryGeometry.false D.sourceOrbit (hbinary F hn hF)
    · have hpos := F.degree_pos
      exact DoubledLinearBounds.false D.sourceOrbit T (hlinear F (by omega) hF) hT hFF hpos
  · exact DoubledSymplecticBounds.false D.sourceOrbit T (hsymplectic F hn hF) hT
  · exact DoubledSymplecticBounds.false D.sourceOrbit T (hsix hF) hT
  · exact hnon (hff n hn hF)
  · exact DoubledSevenBounds.false D.sourceOrbit T (hseven σ hσ hF) hT hFF

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
