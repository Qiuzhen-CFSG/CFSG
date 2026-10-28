module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCentralizer.Reduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCentralizer.IncidentStructure.Extraspecial

/-!+# The incident-pair structure in B.5.1(6)

The actual stabilizer of a nonzero incident vector and covector has an
extraspecial two-core of order `2^(1+2*(d-2))`. Its action on the middle flag
section identifies the quotient with PSL_(d-2)(2). These calculations
discharge the core-structure input of the published Sylow centralizer
reduction. The independent offender exclusion remains explicit in the
consumer theorem below.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(6),
printed pp.99 and 103.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open BinaryNaturalDual BinaryNaturalDual.VectorStabilizers
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer

/-- The core structure of the literal incident-pair stabilizer in dimensions four and five. -/
theorem incident_core_structure {d : ℕ} (hd : d = 4 ∨ d = 5)
    (x : Space d) (f : Module.Dual (ZMod 2) (Space d))
    (hx : x ≠ 0) (hf : f ≠ 0) (h : f x = 0) :
    IsExtraspecial 2 (pCore 2 (pairStabilizer x f)) ∧
    Nat.card (pCore 2 (pairStabilizer x f)) = 2 ^ (1 + 2 * (d - 2)) ∧
    Nonempty ((pairStabilizer x f ⧸ pCore 2 (pairStabilizer x f)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin (d - 2)) (ZMod 2)) := by
  refine ⟨IsExtraspecial.of_mulEquiv (IncidentStructure.coreRadicalEquiv hf h).symm
    (IncidentStructure.radical_extraspecial ?_ hx hf h), ?_,
    ⟨IncidentStructure.incidentQuotientEquiv (by omega) hx hf h⟩⟩
  · simpa only [OuterCyclic.Space, Module.finrank_pi, Fintype.card_fin] using
      (show 3 ≤ d by omega)
  · simpa only [OuterCyclic.Space, Module.finrank_pi, Fintype.card_fin] using
      IncidentStructure.incident_core_card hx hf h

/-- B.5.1(6) with its core-structure calculation discharged. The remaining
offender exclusion is owned by the independent incident-offender calculation. -/
theorem sylowFixedCentralizer_of_incident_offender_exclusion {d : ℕ} (hd : d = 4 ∨ d = 5)
    (ho : ∀ (x : Space d) (f : Module.Dual (ZMod 2) (Space d)),
      x ≠ 0 → f ≠ 0 → f x = 0 →
      ∀ A : Subgroup (LinearGroup d), IsOffender naturalDualRepresentation A →
        ¬ A ≤ PointCores.incidentRadical x f)
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin d) (ZMod 2))) :
    Nonempty (SylowFixedCentralizer (slAction d) ⊤ d T) :=
  sylowFixedCentralizer_of_incident_calculations hd (incident_core_structure hd) ho T

end CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer
