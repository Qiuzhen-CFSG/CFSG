module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.OrbitAction.Checks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.OrbitAction.NeighborData

/-!
# Exhaustive neighbor certificates for the Hall–Janko subgroup graph

Three Schreier words in the full vertex normalizer connect the 36 displayed
rows. Every remaining nonbase row has a product with the base generator
whose sixth power moves a specified point. Since every element of A₄ has
sixth power one, those joins cannot be A₄. These tests use literal products
in the 100-point representation, not graph parameters.

Source: Aschbacher, *Sporadic Groups*, 47.5(2), p.263.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.OrbitAction
open Theory.GroupTheory GeneratorPair FirstFusion Data
set_option maxRecDepth 100000
set_option Elab.async false

def permRep (i : Fin 280) : Equiv.Perm (Fin 100) := evalWord permLetter (words i)
def normalizerPerm (s : Fin 3) : Equiv.Perm (Fin 100) :=
  let q := normalizerGenerator s
  permRep q.1 * permLetter q.2 * (permRep (nextRow q.1 q.2))⁻¹

theorem normalizer_value : ∀ (s : Fin 3) (p : Fin 100),
    normalizerValue s p = normalizerPerm s p := by
  apply allFin
  decide +kernel

theorem normalizer_inv_value : ∀ (s : Fin 3) (p : Fin 100),
    normalizerInvValue s p = (normalizerPerm s)⁻¹ p := by
  apply allFin
  decide +kernel

theorem neighbor_tree : ∀ j : Fin 36, j ≠ 0 → (neighborParent j).val < j.val := by
  apply allFin
  decide +kernel

theorem neighbor_transitions : ∀ (j : Fin 36) (p : Fin 100), j ≠ 0 →
    signedValue (neighborRow j) (neighborFlip j) p =
      normalizerValue (neighborLetter j)
        (value (neighborRow (neighborParent j)) (normalizerInvValue (neighborLetter j) p)) := by
  apply allFin
  decide +kernel

def cPerm : Equiv.Perm (Fin 100) := tableB⁻¹ * tableA * tableB

theorem neighbor_zero_value : ∀ p : Fin 100,
    value (neighborRow 0) p = (cPerm * xPerm * cPerm⁻¹) p := by
  apply allFin
  decide +kernel

theorem neighbor_rows_injective : Function.Injective neighborRow := by
  decide +kernel

theorem isNeighbor_iff : ∀ i : Fin 280,
    isNeighbor i = true ↔ ∃ j : Fin 36, neighborRow j = i := by
  apply allFin
  decide +kernel

def productValue (i : Fin 280) (p : Fin 100) : Fin 100 :=
  value 0 (signedValue i (obstructionSign i) p)

theorem nonneighbor_obstruction : ∀ i : Fin 280, i ≠ 0 → isNeighbor i = false →
    (productValue i)^[6] (obstructionPoint i) ≠ obstructionPoint i := by
  apply allFin
  decide +kernel

end Sporadic.LeechRelated.J2.RecognitionGeometry.OrbitAction
