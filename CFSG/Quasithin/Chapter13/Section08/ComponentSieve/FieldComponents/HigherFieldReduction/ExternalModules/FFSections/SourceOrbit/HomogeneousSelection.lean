module

public import CFSG.Quasithin.ChapterA.Section01.Representations.HomogeneousBridge
public import Theory.GroupTheory.Covering

/-!
# Homogeneous selection for the actual quasisimple actor

Quasisimplicity supplies both perfectness and nontriviality. Faithfulness of
the specified representation therefore supplies an Irr⁺ seed, and A.1.42
selects a homogeneous member for the actual Sylow subgroup. The Chapter A
bridge retains the original fixed-space quotient and its quotient map.

Source: Aschbacher–Smith, A.1.40–42, pp.31–32; application in the proof of
13.8.20(a), p.954, combined manuscript of 1 March 2004.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit

/-- Homogeneous existence uses the faithful source action, not merely its
compatibility with conjugation. No selected constituent is a premise. -/
theorem exists_homogeneous_of_quasisimple
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hfaith : Function.Injective ρ)
    (K : Subgroup D) [K.Normal] [IsQuasisimple K] (P : Sylow 2 D) :
    ∃ I : Submodule (ZMod 2) V, IsIrrPlusWith ρ K P I := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  have : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hK : K ≠ ⊥ := by
    intro he
    obtain ⟨k, hk⟩ := exists_ne (1 : K)
    apply hk
    apply Subtype.ext
    exact mem_bot.mp (he ▸ k.property)
  exact ChapterA.exists_chapter15_isIrrPlusWith_of_faithful ρ hfaith K P hK
    le_normalizer_of_normal P.isPGroup'

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit
