module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityActionPairConstruction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityActionPairOrbit

/-!
# Canonical equality action-pair assembly

The full known-simple action classification, larger-model exclusions and
literal two-conjugate construction supply every field of the canonical
pair contract. In particular, the natural-action and center premises of
the orbit calculation are discharged here. The only local-analysis premise
is the earlier-source package explicitly allowed in this construction.

This is the action-pair part of 6.2.13. The subsequent extension and transfer
argument is owned by the equality-geometry assembly; no splitting of H/P
or self-centralization of P is included.

Source: Aschbacher–Smith, Proposition 6.2.13, printed pp.686–687
(PDF pp.703–704).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- Construct the canonical pair/core/orbit package from the original equality
hypotheses, discharging the natural-action model and all local lift premises. -/
theorem LocalAnalysis.equality_action_pair_data
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    EqualityActionPairData (T : Subgroup G) L M R z := by
  obtain ⟨hpair, hquot, hplus, hres⟩ :=
    A.equality_canonical_pair_core h611 hnatural hz horder hTH hbranch
  have hcenter := A.equalityCore_center h611 hz horder hplus
  exact {
    pair := hpair
    quotient := hquot
    plusType := hplus
    core_center := hcenter
    plane_le_core := A.equalityPlane_le_equalityCore h611 hz
    natural_orbit := A.equality_naturalFourOrbit_of_center h611 hz
      (A.equality_natural_action h611 hnatural hz horder hTH hbranch) hcenter
    generation := A.equalityLayerClosure_sup_sylow h611 hnatural hz horder hTH hbranch
    core_residual := hres }

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
