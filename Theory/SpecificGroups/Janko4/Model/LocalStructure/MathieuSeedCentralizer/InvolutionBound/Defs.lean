module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.Seeds
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount

/-!
# Fibers for counting involutions in the local seed centralizer

All carriers here are subgroups or quotients of the literal matrix-defined
max1 subgroup. The quotient classes retain membership in the image of the
actual seed centralizer. The fibers retain ambient conjugacy to the actual
seed, so their cardinalities count all possible kernel lifts.

These definitions support the local count used in the Thompson order argument
of Aschbacher--Smith, `refs/quasithin.pdf`, A.6, printed pp.64--65. They assert
no equality with the full ambient centralizer and use no ambient group order.
-/

@[expose] public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound
open Cardinality Simplicity.Max1Fusion

variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

abbrev Local := max1Subgroup hA hB
abbrev Quotient := LocalQuotient hA hB

/-- Centralizer of the seed inside the actual max1 subgroup. -/
def centralizer : Subgroup (Local hA hB) :=
  Subgroup.centralizer ({localKernelSeed hA hB} : Set (Local hA hB))

/-- The literal inclusion into the original matrix carrier. -/
def inclusion : centralizer hA hB →* Model :=
  (max1Subgroup hA hB).subtype.comp (centralizer hA hB).subtype

/-- The original quotient by the 2048-element binary kernel. -/
def projection : Local hA hB →* Quotient hA hB :=
  QuotientGroup.mk' (localKernel hA hB)

/-- Lifts of the two quotient involution representatives. The second lift
has square equal to the seed; no split extension is assumed. -/
def base (b : Bool) : Local hA hB :=
  if b then (localX hA hB * localY hA hB)^7 else localX hA hB

/-- A quotient conjugacy class restricted to the image of the local centralizer. -/
abbrev QuotientClass (b : Bool) :=
  {q : Quotient hA hB //
    q ∈ (centralizer hA hB).map (projection hA hB) ∧
    IsConj (projection hA hB (base hA hB b)) q}

/-- Ambient seed-type elements in a specified quotient fiber. -/
abbrev ColoredFiber (q : Quotient hA hB) :=
  {w : Local hA hB // IsConj (localKernelSeed hA hB : Model) (w : Model) ∧
    projection hA hB w = q}

/-- The two distinguished fibers to which quotient conjugacy reduces counting. -/
abbrev BaseFiber (b : Bool) :=
  ColoredFiber hA hB (projection hA hB (base hA hB b))

/-- The precise set to be bounded, inside the actual local centralizer. -/
abbrev SeedType :=
  {u : centralizer hA hB // IsConj (localKernelSeed hA hB : Model) (inclusion hA hB u)}

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localX localY
  localKernelSeed localKernel

/-- The seed is an involution, by its checked ambient fusion. -/
theorem seed_order : orderOf (localKernelSeed hA hB : Model) = 2 := by
  obtain ⟨g, hg⟩ := seed_fuses_second hA hB
  have ho := orderOf_injective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective (localKernelSeed hA hB : Model)
  change orderOf (g * (localKernelSeed hA hB : Model) * g⁻¹) = _ at ho
  rw [← hg] at ho
  exact ho.symm.trans (Simplicity.involutionRepresentative_one_orderOf hA hB)

/-- Ambient seed type already implies order two in max1. -/
theorem colored_order (w : Local hA hB)
    (hw : IsConj (localKernelSeed hA hB : Model) (w : Model)) : orderOf w = 2 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hw
  have ho := orderOf_injective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective (localKernelSeed hA hB : Model)
  change orderOf (g * (localKernelSeed hA hB : Model) * g⁻¹) = _ at ho
  rw [hg] at ho
  rw [← orderOf_injective (max1Subgroup hA hB).subtype Subtype.val_injective]
  exact ho.trans (seed_order hA hB)

end Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound
