module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure
-- Internal extension of the source core definition; its body stays private.
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Minimal parabolics with maximal Sylow subgroups

A maximal nonnormal Sylow two-subgroup is its own unique maximal overgroup.
Its normal core is exactly the two-core: it is a normal two-subgroup, and
every normal two-subgroup lies in every Sylow subgroup. This identifies the
literal core in B.6.8 for the wreath-quotient application to Definition 1.3.1.

Source: Aschbacher--Smith B.6.1 and B.6.8, printed pp.112--114.
-/

open Subgroup
namespace CFSG.Quasithin.ChapterB
variable {K : Type*} [Group K]
/-- A maximal nonnormal Sylow subgroup makes the whole group minimal parabolic. -/
public theorem isMinimalParabolicOver_of_sylow_isCoatom (S : Sylow 2 K) (hmax : IsCoatom (S : Subgroup K))
    (hn : ¬ (S : Subgroup K).Normal) : IsMinimalParabolicOver S ⊤ := by
  apply (isMinimalParabolicOver_top_iff S).mpr
  refine ⟨⟨(S : Subgroup K), ⟨hmax,le_rfl⟩,?_⟩,hn⟩
  intro M hM
  exact (hmax.le_iff_eq hM.1.ne_top).mp hM.2

/-- If the Sylow itself is maximal, the source maximal core is the two-core. -/
public theorem minimalParabolicCore_eq_twoCore_of_sylow_isCoatom
    (S : Sylow 2 K) (hP : IsMinimalParabolicOver S ⊤)
    (hmax : IsCoatom (S : Subgroup K)) :
    minimalParabolicCore S hP = pCore 2 K := by
  have he : minimalParabolicMax S hP = (S : Subgroup K) :=
    (minimalParabolicMax_unique S hP hmax le_rfl).symm
  apply le_antisymm _ (minimalParabolicTwoCore_le_core S hP)
  change (minimalParabolicMax S hP).normalCore ≤ _
  rw [he]
  exact le_sSup ⟨inferInstance,S.isPGroup'.to_le (normalCore_le _)⟩
end CFSG.Quasithin.ChapterB

