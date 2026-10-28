module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SectionCoordinates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.Selection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.Assembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SeedAction

/-!
# The external FF constituent on the source carrier

The complete F.9.18(4) conclusion, once supplied by the earlier source
implication, selects its invariant FF alternative on the literal U_H/V₁.
Both excluded cases are proved: ambient invariance contradicts the cubic
pair decomposition, and the nonisomorphic hatted pair contradicts Schur's
lemma and the same decomposition on the actual quotient image.

`exists_source_orbit_of_full_f918` constructs the homogeneous constituent,
its actual two-conjugate orbit, its multiplicity identification and the
faithful central action satisfying B.4.2. The complete earlier F.9.18(4)
implication and the parent's source structural outputs remain explicit;
the full standing hypotheses are specified in `SourceOrbit.FullSource`.
No natural-module classification or external-branch contradiction is asserted.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.20, printed pp.954–955; F.9.18(4), printed pp.325–326.
-/

@[expose] public noncomputable section

open Representation Representation.BinaryOffender InvertedCubicTensor
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit

variable {G : Type*} [Group G] (H K X V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  [(Source.starImage H K).Normal]

/-- The marked source cubic image excludes both unwanted alternatives on the
actual source carrier. The earlier conclusion and homogeneous member remain explicit. -/
theorem source_ff_of_fourConclusion
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (P : Sylow 2 (Source.Hstar H)) (s : S₃ →* Source.Hstar H)
    (hs : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X)
    (hgen : subspaceCommutator ρ ⊤ (Source.starImage H X) = ⊤)
    (earlier : FourConclusion ρ (Source.starImage H K) P)
    (I : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁))
    (hI : IsIrrPlusWith ρ (Source.starImage H K) P I) :
    ∃ hIP : (P : Subgroup (Source.Hstar H)) ≤ subspaceStabilizer ρ I,
      orbitSpan ρ P I = I ∧
      IsFFModule (imageRepresentation
        (constituentAction ρ (Source.starImage H K) P I hI.invariant hIP)) :=
  ff_of_fourConclusion ρ (Source.starImage H K) P s hs
    (by rw [hmark]; exact hgen) earlier I hI

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit
