module

public import Theory.AtlasPort.LinearGroups.G2.Simplicity
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Finite universal central covers of the octonion G₂ model

For a finite field with more than two elements the actual split-octonion
automorphism group is perfect and simple. The derived subgroup of its free
central extension therefore gives a finite quasisimple universal cover.
Its kernel is its center, and its central quotient is the original model.

These constructions fix the carriers and projection for the separate kernel
calculations in Aschbacher–Smith I.1.3–I.1.4, printed pp.407–408. No kernel
order is asserted here. In particular the cover over GF(4) has not yet been
identified as a double cover. The field-two endpoint is deliberately excluded:
the source simple group there is G₂(2)′, identified with PSU₃(3).

The octonion model and its simplicity proof come from the attributed ATLAS
ports imported above; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

namespace Atlas.G2.FiniteCover

open Theory.GroupTheory PerfectCentralCovering

universe u w

/-- The actual free-central-extension construction over the octonion model. -/
public abbrev CoverGroup (F : Type u) [Field F] := UniversalGroup (Model F)

/-- The literal kernel to be calculated, independent of any chosen covering. -/
public abbrev Kernel (F : Type u) [Field F] := (universalProjection (Model F)).ker

variable (F : Type u) [Field F] [Finite F] [Fact (2 < Nat.card F)]

public instance model_isPerfect : Group.IsPerfect (Model F) := Atlas.G2.isPerfect Fact.out

public instance model_isSimple : IsSimpleGroup (Model F) := Atlas.G2.isSimple Fact.out

public instance model_isQuasisimple : IsQuasisimple (Model F) where
  toIsPerfect := inferInstance
  simple := by
    have hc : Subgroup.center (Model F) = ⊥ := by
      rcases (inferInstance : (Subgroup.center (Model F)).Normal).eq_bot_or_eq_top with h | h
      · exact h
      · exact False.elim (Group.IsPerfect.not_isMulCommutative (Model F)
          (Subgroup.center_eq_top_iff.mp h))
    exact ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup

/-- The finite quasisimple universal covering of the actual G₂(F). -/
@[expose] public def cover : Covering (CoverGroup F) (Model F) :=
  universalQuasisimpleCover (Model F)

/-- Universality for finite quasisimple covers in any target universe. -/
public theorem cover_isUniversal : Covering.IsUniversal.{u, u, w} (cover F) :=
  universalQuasisimpleCover_isUniversal (Model F)

/-- The kernel of this covering is the whole center of the covering group. -/
public theorem kernel_eq_center :
    (universalProjection (Model F)).ker = Subgroup.center (CoverGroup F) :=
  (cover F).ker_eq_center_of_isSimple

/-- An actual central-quotient identification, with the prescribed G₂ base. -/
public noncomputable def quotientCenterEquiv :
    CoverGroup F ⧸ Subgroup.center (CoverGroup F) ≃* Model F :=
  (QuotientGroup.quotientMulEquivOfEq (kernel_eq_center F).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (universalProjection (Model F))
      (cover F).surjective)

/-- The distinguished field-four carrier for the exceptional multiplier. -/
public abbrev FourField := GaloisField 2 2

public instance fourField_large : Fact (2 < Nat.card FourField) := ⟨by
  rw [GaloisField.card 2 2 (by decide)]
  decide⟩

/-- The base is the octonion automorphism group over GF(4). -/
public noncomputable abbrev FourBase := Model FourField

/-- The canonical universal cover, whose kernel order remains to be computed. -/
public noncomputable abbrev FourCover := CoverGroup FourField

end Atlas.G2.FiniteCover
