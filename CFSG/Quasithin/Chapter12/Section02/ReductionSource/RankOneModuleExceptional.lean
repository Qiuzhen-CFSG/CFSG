module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleInputs
public import Stellmacher.OmegaOneCenterMap

/-!
# Retaining the exceptional local configuration in source 5.2.3(1)

The exceptional branch identifies the commutator module and places the
actual two-residual of H in a C-component of C_G(Ω₁(Z(T))). The component
is relative to that centralizer. Both residual comparisons use their
literal embeddings in G, and all quotient identifications are actual
isomorphisms. The module assembly may forget this geometry, but it must
not replace the exceptional branch by n(H) = 1.

The binary exponent equals two by `exponent_eq_two_of_psl_and_a5` once the
module branch is consumed. `GenericConfigurationExit` is an explicit
missing source input, not an assertion of 5.2.3.
Source: Aschbacher--Smith, 5.2.3(1), printed p.649 (PDF p.666).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]

/-- All exceptional residual/component geometry, with the needed whole-layer
module conclusion. The field exponent is recoverable from the concrete actor. -/
def ExceptionalExit (T : Sylow 2 G) (L H : Subgroup G) : Prop :=
  Chapter6.Source.IsOneOrTwoA5Modules L (commutatorLayer T L) ∧
    ∃ KZ : Subgroup (centralizer (Stellmacher.omegaOneCenterAmbient
        (T : Subgroup G) : Set G)),
      KZ.IsCComponent ∧
      (pResidual 2 H).map H.subtype ≤ KZ.map
        (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)).subtype ∧
      ((ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
          (Nonempty ((KZ ⧸ pCore 2 KZ) ≃* alternatingGroup (Fin 7)) ∨
           Nonempty ((KZ ⧸ pCore 2 KZ) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
           Nonempty ((KZ ⧸ pCore 2 KZ) ≃* Sporadic.Mathieu.M23))) ∨
        ((pResidual 2 H).map H.subtype = KZ.map
            (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)).subtype ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4))

/-- The generic producer retains the full exceptional alternative. The global
rank-two exponent must already be greater than one in this specialization. -/
def GenericConfigurationExit (T : Sylow 2 G) (L : Subgroup G) : Prop :=
  Chapter3.HasMaximalOutside T (normalizer (L : Set G)) →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      1 < ChapterE.generationParameter H → ExceptionalExit T L H ∨ GlobalExit G

/-- Merge only the module clause of the exceptional branch; no assertion
about the other outside generation parameters is made. -/
theorem genericExit_of_configuration {T : Sylow 2 G} {L : Subgroup G}
    (h : GenericConfigurationExit T L) : GenericExit T L := by
  intro hout H hH hn
  exact (h hout H hH hn).imp And.left id

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
