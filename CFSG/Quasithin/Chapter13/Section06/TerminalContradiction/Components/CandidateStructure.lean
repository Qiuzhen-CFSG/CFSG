module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.ThreeStructure.Models
public import Theory.GroupTheory.CComponent.CenterlessRankNormal
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison
public import Theory.AtlasPort.Janko2.Sporadic.Janko2

/-!
# Normality and quasisimplicity of the exceptional candidate

The actual J₂, M₂₃ and PSL₃(4) identifications make the candidate's
two-core quotient simple. Perfection inherited from the C-component and
its proved trivial center give quasisimplicity. The three-rank of that
quotient is at least two; distinct conjugate components would violate the
ambient SQTK rank bound. Hence the candidate is normal in the local group.

These deductions discharge the structural premises needed to isolate the
candidate in the original 13.6.27 argument. They do not select the candidate.
Source: Aschbacher–Smith, A.3.8(3), printed p.46, and 13.6.27, pp.934–935.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components
universe u
variable {H : Type u} [Group H] {T K : Subgroup H}

/-- The literal quotient in every exceptional candidate is simple. -/
theorem Candidate.quotient_isSimple (hc : Candidate T K) :
    IsSimpleGroup (K ⧸ pCore 2 K) := by
  rcases hc with hJ | hM | ⟨e, _⟩
  · obtain ⟨e⟩ := hJ
    let := Atlas.Sporadic.Janko2.isSimpleGroup
    let : IsSimpleGroup Sporadic.LeechRelated.J2.Carrier :=
      Sporadic.LeechRelated.J2.IcosianComparison.comparison.isSimpleGroup
    exact e.isSimpleGroup
  · obtain ⟨e⟩ := hM
    let := Sporadic.Mathieu.m23_isSimpleGroup
    exact e.isSimpleGroup
  · let : IsSimpleGroup L3Four := Atlas.psl_simple_high_rank 3 (by decide)
    exact e.isSimpleGroup

/-- Perfection of the original component makes its simple quotient
quasisimple; this is no longer an additional source premise. -/
theorem Candidate.quotient_isQuasisimple (hc : Candidate T K) (hK : K.IsCComponent) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  let := hK.perfect
  let := hc.quotient_isSimple
  exact { simple := ((QuotientGroup.quotientMulEquivOfEq
    (ThreeStructure.candidate_center_eq_bot hK hc)).trans QuotientGroup.quotientBot).isSimpleGroup }

variable [Finite H]

/-- The source rank bound forces every exceptional C-component candidate
to be normal, before the uniqueness argument. -/
theorem Candidate.normal {C : GroupClass.{u}} (hc : Candidate T K)
    (hK : K.IsCComponent) (hH : IsSQTK C H) : K.Normal := by
  let := hc.quotient_isQuasisimple hK
  exact hK.normal_of_centerless_core_threeRank
    (ThreeStructure.candidate_center_eq_bot hK hc)
    (ThreeStructure.candidate_three_rank_ge_two hc)
    (hH.stronglyQuasithin 3 (by decide) (by decide))

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components
