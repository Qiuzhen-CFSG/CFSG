module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.Models
public import Theory.GroupTheory.Covering

/-!
# Remaining odd linear and unitary representation restrictions

These propositions specify the two remaining representation-theoretic inputs
for the odd linear/unitary branch of B.1.13. They are obligations, not assertions
of the classification. The linear output keeps the three exceptional rank-one
parameters; the unitary output treats dimensions at least three. Dimension two
is handled by an actual PSU₂–PSL₂ comparison in the assembly.

Only the faithful action image is used here. The assembly descends the original
central-kernel action using `BinaryOffender.CentralKernelImage`, which preserves
the literal full linear normalizer and the simple central quotient.

Sources: Aschbacher–Smith, B.1.13, B.4.4 and K.2, printed pp.73–74, 87 and 453;
Guralnick–Malle, *Classification of 2F-modules, I*, §4A–B and Table 6.5;
*Classification of 2F-modules, II*, Theorem B, Table 2 and §9.
The original preprints are available at
https://agag-malle.math.rptu.de/~malle/download/failfact.dvi and
https://agag-malle.math.rptu.de/~malle/download/failfactlie.dvi.

The classification assumes absolute irreducibility and quasisimple F* for its
acting group. Neither condition on the full normalizer is assumed by these
contracts. A proof using that classification must construct an appropriate
acting group and coefficient field. Moreover, Table 6.5 of part I admits
triple covers of PSU₄(3) as 2F-modules: their exclusion needs the sharper
F-module inequality, including possible outer offenders. These hypotheses
cannot be discharged merely by reading the list of quasisimple F-modules.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary

universe u

/-- The numerical odd-field linear restriction, still to be proved. -/
def LinearRestriction : Prop :=
  ∀ {L W : Type u} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) L W),
    Function.Injective σ → σ.IsIrreducible →
    IsFFModule (normalizerRepresentation σ) →
    ∀ {n q : ℕ}, KnownSimple.LinearParameters n q → Odd q →
      ClassicalGroup.IsPSL (L ⧸ center L) n q →
      n = 2 ∧ (q = 5 ∨ q = 7 ∨ q = 9)

/-- The numerical odd-field unitary restriction above dimension two,
still to be proved. It includes the exceptional triple PSU₄(3) covers. -/
def UnitaryRestriction : Prop :=
  ∀ {L W : Type u} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) L W),
    Function.Injective σ → σ.IsIrreducible →
    IsFFModule (normalizerRepresentation σ) →
    ∀ {n q : ℕ}, KnownSimple.UnitaryParameters n q → 3 ≤ n → Odd q →
      ClassicalGroup.IsPSU (L ⧸ center L) n q → n = 3 ∧ q = 3

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary
