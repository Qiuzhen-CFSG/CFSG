module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SectionCoordinates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.PairExclusion
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance.Inputs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Models

/-!
# Selecting the invariant FF alternative

`FourConclusion` retains the component clause and all three alternatives
of F.9.18(4), universally over the homogeneous Irr⁺ constituents of a fixed
action. Its FF alternative uses the actual faithful action image of KT on
I. The third alternative retains the natural action models, the separate
four-dimensional A₇ case, the actual hatted pair and its nonisomorphism.

The external commuting cubic action excludes (i) and (iii). Thus every
specified member of Irr⁺(K,V,T) is T-invariant and is an FF-module for its
KT action image. The orbit identity follows from invariance.

This is a deduction from the complete earlier conclusion, not a theorem
asserting F.9.18 under arbitrary representation hypotheses. Constructing
that conclusion from the full F.9 setup, homogeneous existence, the actual
two-conjugate H-orbit, and the B.4.2 action-image premises remain separate
assembly obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.18(4),
printed pp.325–326; proof of 13.8.20, printed p.954.
-/

@[expose] public noncomputable section

open Representation Representation.BinaryOffender InvertedCubicTensor

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
open CFSG.Quasithin.Chapter13.Section08.Components.Models
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
  (P : Sylow 2 G) (s : S₃ →* G)
  (hs : ∀ (k : L) g, Commute (k : G) (s g))

include hs in
/-- The nonisomorphic hatted pair in F.9.18(4iii) contradicts the external cubic action. -/
theorem not_hattedNaturalPair
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlusWith ρ L P I) :
    ¬ HattedNaturalPair ρ L P I hI := by
  intro hp
  obtain ⟨t, _, he, hd, hne⟩ := hp.pair
  exact hne (hatted_pair_isomorphic ρ L s hs hgen I (rightConjugate ρ I t)
    hI.isIrrPlus
    (hI.isIrrPlus.map_normalizer ρ (hI.normalizes (P.inv_mem t.property))) hd he)

/-- The literal KT-action on the selected invariant constituent. -/
def constituentAction (I : Submodule (ZMod 2) V)
    (hIL : L ≤ subspaceStabilizer ρ I) (hIP : (P : Subgroup G) ≤ subspaceStabilizer ρ I) :=
  (invariantSubspace ρ (L ⊔ (P : Subgroup G)) I (sup_le hIL hIP)).toRepresentation

/-- The complete conclusion of (4) at a fixed source action. This is an earlier
conclusion to be obtained from the full source hypotheses, not an unconditional theorem. -/
structure FourConclusion : Prop where
  component : F918Models L
  alternatives : ∀ (I : Submodule (ZMod 2) V) (hI : IsIrrPlusWith ρ L P I),
    (⊤ ≤ subspaceStabilizer ρ I) ∨
    (∃ hIP : (P : Subgroup G) ≤ subspaceStabilizer ρ I,
      IsFFModule (imageRepresentation (constituentAction ρ L P I hI.invariant hIP))) ∨
    HattedNaturalPair ρ L P I hI

include hs in
/-- Excluding the first and third alternatives selects the genuine invariant FF action. -/
theorem ff_of_fourConclusion
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤)
    (earlier : FourConclusion ρ L P)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlusWith ρ L P I) :
    ∃ hIP : (P : Subgroup G) ≤ subspaceStabilizer ρ I,
      orbitSpan ρ P I = I ∧
      IsFFModule (imageRepresentation (constituentAction ρ L P I hI.invariant hIP)) := by
  rcases earlier.alternatives I hI with hinv | hff | hpair
  · exact (irrPlus_not_invariant ρ s L hs hgen I hI.isIrrPlus hinv).elim
  · obtain ⟨hIP, hff⟩ := hff
    exact ⟨hIP, orbitSpan_eq_self ρ hIP, hff⟩
  · exact (not_hattedNaturalPair ρ L P s hs hgen I hI hpair).elim
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit
