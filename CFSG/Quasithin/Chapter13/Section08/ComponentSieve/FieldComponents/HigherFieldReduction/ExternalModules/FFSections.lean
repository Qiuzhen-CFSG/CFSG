module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SectionCoordinates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.Assembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SeedAction

/-!
# Source sections and external FF alternatives

The section maps use the literal binary module U_H/V₁, with X* marked by
the embedded alternating subgroup of S₃. `source_alternatives` now constructs
the actual selected FF constituent, its two-conjugate orbit and the compatible
central-quotient maps before applying the complete B.4.2 list. It excludes the
unitary family and produces natural L₂/L₃ tensor sections or full marked
exceptional coordinates on the moved module W = [U,K*].

`source_natural_alternatives` eliminates the latter branch using the earlier
rank implication and the actual critical conjugate placement and quadraticity.
Both natural branches retain their original Borel markings and central layers.
The genuine structural setup and complete earlier theorem implications remain
explicit parent inputs; the full 13.8.20 is not asserted here. No W = U,
B-centralization or fixed-space equality is assumed. The earlier section APIs
below, and all conditional whole-U APIs, remain available.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.20, printed pp.954–955 (PDF pp.971–972).
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor
open scoped TensorProduct IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections

variable {G : Type*} [Group G] (H K X V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
  (s : S₃ →* Source.Hstar H)
  (hs : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g))
  (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X)
  (hgen : subspaceCommutator ρ ⊤ (Source.starImage H X) = ⊤)

include hs hmark hgen in
/-- The source cubic marking excludes the ambient-invariant F.9.18(4i) case. -/
theorem source_irrPlus_not_invariant [(Source.starImage H K).Normal]
    (I : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁))
    (hI : IsIrrPlus ρ (Source.starImage H K) I) :
    ¬ (⊤ : Subgroup (Source.Hstar H)) ≤ subspaceStabilizer ρ I :=
  irrPlus_not_invariant ρ s (Source.starImage H K) hs
    (by rw [hmark]; exact hgen) I hI

variable {L N : Type*} [Group L] [AddCommGroup N] [Module (ZMod 2) N]
  (σ : Representation (ZMod 2) L N) (e : Source.starImage H K ≃* L)
  (C D : Subrepresentation ρ)

/-- A recognized multiplicity factor constructs tensor coordinates on the source section.
This preserves the supplied component marking and works in either natural orientation. -/
def sourceTensorLayer (hCD : C ≤ D)
    (a : SectionMultiplicity ρ s C D ≃ₗ[ZMod 2] N)
    (ha : ∀ k v, a (sectionMultiplicityAction ρ (Source.starImage H K).subtype s hs C D k v) =
      σ (e k) (a v)) :
    NaturalLayers.TensorLayer (ρ.comp (Source.starImage H K).subtype) σ e
      C.toSubmodule D.toSubmodule :=
  tensorLayer ρ (Source.starImage H K).subtype s hs C D σ e a hCD
    (by rw [hmark]; exact hgen) ha

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections
