module

public import Theory.Representation.MathieuCodeRestriction.Construction
public import Theory.Representation.SubspaceQuotient

/-!
# The eleven-dimensional Mathieu code and cocode actions

The code is the literal quotient of the Golay space by its constant line.
The cocode is the literal quotient of the even-weight core by the Golay space.
The native permutation action descends to both quotients; rank-nullity gives
dimension eleven in each case.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.13.1,
printed p.395. No irreducibility or chapter parameter table is assumed.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu
open scoped BigOperators Pointwise

namespace MathieuCode

def golaySubrepresentation : Subrepresentation fullRepresentation where
  toSubmodule := golay
  apply_mem_toSubmodule g _ hv := golay_invariant g hv

def golayRepresentation : Representation (ZMod 2) M24 golay :=
  golaySubrepresentation.toRepresentation

/-- The all-ones line, as a subspace of the Golay code. -/
def codeLine : Submodule (ZMod 2) golay :=
  (BinaryPermutation.constants (Fin 24)).comap golay.subtype

abbrev Code := golay ⧸ codeLine

def codeLineSubrepresentation : Subrepresentation golayRepresentation where
  toSubmodule := codeLine
  apply_mem_toSubmodule g _ hv := BinaryPermutation.constants_invariant (Fin 24) g.val hv

/-- The M₂₄ action on the eleven-dimensional code quotient. -/
def codeRepresentation : Representation (ZMod 2) M24 Code :=
  codeLineSubrepresentation.quotientRepresentation

abbrev Core := BinaryPermutation.core (Fin 24)

def coreRepresentation : Representation (ZMod 2) M24 Core :=
  (BinaryPermutation.coreRepresentation (Fin 24)).comp M24.subtype

/-- The Golay code, as a subspace of the even-weight core. -/
def codeInCore : Submodule (ZMod 2) Core := golay.comap Core.subtype

abbrev Cocode := Core ⧸ codeInCore

def codeInCoreSubrepresentation : Subrepresentation coreRepresentation where
  toSubmodule := codeInCore
  apply_mem_toSubmodule g _ hv := golay_invariant g hv

/-- The M₂₄ action on the eleven-dimensional cocode quotient. -/
def cocodeRepresentation : Representation (ZMod 2) M24 Cocode :=
  codeInCoreSubrepresentation.quotientRepresentation

theorem codeRepresentation_mk (g : M24) (v : golay) :
    codeRepresentation g (codeLine.mkQ v) = codeLine.mkQ (golayRepresentation g v) := rfl

theorem cocodeRepresentation_mk (g : M24) (v : Core) :
    cocodeRepresentation g (codeInCore.mkQ v) = codeInCore.mkQ (coreRepresentation g v) := rfl

theorem finrank_codeLine : Module.finrank (ZMod 2) codeLine = 1 := by
  exact (Submodule.comapSubtypeEquivOfLe constants_le_golay).finrank_eq.trans
    (BinaryPermutation.finrank_constants (Fin 24))

theorem finrank_codeInCore : Module.finrank (ZMod 2) codeInCore = 12 := by
  exact (Submodule.comapSubtypeEquivOfLe golay_le_core).finrank_eq.trans finrank_golay

theorem finrank_code : Module.finrank (ZMod 2) Code = 11 := by
  have h := codeLine.finrank_quotient_add_finrank
  rw [finrank_codeLine, finrank_golay] at h
  change Module.finrank (ZMod 2) Code + 1 = 12 at h
  omega

theorem finrank_cocode : Module.finrank (ZMod 2) Cocode = 11 := by
  have h := codeInCore.finrank_quotient_add_finrank
  rw [finrank_codeInCore, BinaryPermutation.finrank_core] at h
  change Module.finrank (ZMod 2) Cocode + 12 = 24 - 1 at h
  omega

end MathieuCode
