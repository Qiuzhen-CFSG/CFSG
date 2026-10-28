module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.BorelAutomorphisms.Data

/-!
Kernel-checked finite certificates for the Borel argument.  The generator words
recover the Sylow factors, while the relation and orbit certificates supply the
only model-specific calculations used by `Coverage.lean`; all are evaluated on
the retained degree-100 permutation carrier.
-/

@[expose] public section
open Subgroup
open Theory.GroupTheory
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.BorelAutomorphisms
open GeneratorPair Seed PairNormalizer
open PairNormalizer.SylowData PairNormalizer.QuotientData
open GeneratorPair.SecondOrbitCertificate

def generatorWord (i : Fin 7) : List (Fin 2) :=
  match i.val with
  | 0 => [1, 1, 0, 1, 1, 0, 0, 1, 0, 1]
  | 1 => [1, 0, 1, 1, 0]
  | 2 => [0, 1, 1, 0, 1, 0, 0, 0, 0]
  | 3 => [1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0]
  | 4 => [1, 0, 0, 1, 1, 0, 0]
  | 5 => [1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0]
  | _ => [0, 0, 0, 0]

set_option maxRecDepth 100000 in
theorem generator_check : ∀ i,
    evalWord ![xTable, oddTable 1] (generatorWord i) = sGenTable i := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem x_relations : xTable ^ 8 = 1 ∧ xTable ^ 4 ≠ 1 ∧
    (xTable * oddTable 1) ^ 6 ≠ 1 ∧ (xTable * (oddTable 1)⁻¹) ^ 6 = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem x_orbit_check : ∀ i : Fin 384,
    bTable i ^ 8 = 1 → bTable i ^ 4 ≠ 1 →
    bTable (xConjIndex i) * xTable * (bTable (xConjIndex i))⁻¹ = bTable i := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem v_orbit_check : ∀ i : Fin 384,
    bTable i ^ 3 = 1 → bTable i ≠ 1 →
    (xTable * bTable i) ^ 6 ≠ 1 → (xTable * (bTable i)⁻¹) ^ 6 = 1 →
    extensionTable (vConjIndex i) * xTable * (extensionTable (vConjIndex i))⁻¹ = xTable ∧
    extensionTable (vConjIndex i) * oddTable 1 * (extensionTable (vConjIndex i))⁻¹ =
      bTable i := by
  apply allFin
  decide +kernel
end Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.BorelAutomorphisms
