module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Factors
public import Theory.PPrimeCore
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# A single local factor for the solvable FF-module argument

This is the output contract for the local construction, not an existence
assertion. For a minimal best offender A, the factor is the actual subgroup
[O₂′(G), A]A. Its support carries the natural SL₂(2)-action and complements
its fixed space. Every other minimal best offender lies in the factor or
centralizes the factor and fixes its support. These are the local facts from
which the finite internal decompositions will be assembled.

Source: Kurzweil–Stellmacher, *The Theory of Finite Groups*, 9.3.3–9.3.6,
printed pp. 241–246 (PDF pp. 254–259 in `refs/original/kurzweil.pdf`),
supporting Aschbacher–Smith B.1.8(1)–(3). The construction must be proved
from solvability, trivial two-core, faithfulness and the offender lemmas.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterB

open Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The concrete local factor attached to a minimal best offender.
No inhabitant is postulated by this declaration. -/
structure SolvableFFLocalBlock (ρ : Representation (ZMod 2) G V) (A : Subgroup G) where
  factor : Subgroup G
  factor_eq : factor = ⁅pPrimeCore 2 G, A⁆ ⊔ A
  factor_le : factor ≤ offenderSubgroup ρ
  factorModel : factor ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
  naturalEquiv : subspaceCommutator ρ ⊤ factor ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)
  naturalEquiv_action : ∀ (g : factor) (v : subspaceCommutator ρ ⊤ factor),
    ρ (g : G) (v : V) =
      (naturalEquiv.symm
        (Representation.specialLinearNatural 2 (factorModel g) (naturalEquiv v)) : V)
  complement : IsCompl (subspaceCommutator ρ ⊤ factor) (fixedSpace ρ factor)
  minimal_offenders : ∀ B, IsMinimalBestOffender ρ B →
    B ≤ factor ∨
      B ≤ Subgroup.centralizer (factor : Set G) ∧
        subspaceCommutator ρ ⊤ factor ≤ fixedSpace ρ B

end CFSG.Quasithin.ChapterB
