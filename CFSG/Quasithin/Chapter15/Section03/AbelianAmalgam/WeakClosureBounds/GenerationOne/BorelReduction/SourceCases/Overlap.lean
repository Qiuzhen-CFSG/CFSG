module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.Quotients
public import CFSG.Quasithin.ChapterB.Section06To07.Structure
public import Theory.GroupTheory.PCoreRestriction
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The minimal-parabolic maximal subgroup is the actual overlap

Every proper overgroup of T in H has nontrivial two-core: it contains O₂(H).
Minimality in H(T,M) therefore puts that overgroup inside M. Applied to the
unique maximal overgroup from B.6.1, maximality identifies it with M ∩ H.
Taking normal cores identifies the source J and supplies O₂(H) ≤ J.

The proof-only `import all` supplies the unexposed definition of the earlier
core for the comparison theorem. Its existing public boundary is preserved;
clients can use the comparison without unfolding that definition.

This is the overlap comparison needed to apply E.2.2 on printed p.1152.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.6.1–8,
printed pp.112–114, E.2.2, pp.215–216, and 15.3.65, p.1152.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction.SourceCases
variable {G : Type*} [Group G]
/-- The unique maximal overgroup from B.6.1 is M ∩ H, internal to H. -/
theorem overlap_eq_minimalParabolicMax
    {T : Sylow 2 G} {H M : Subgroup G}
    (hH : H ∈ minimalSylowOutsideFamily T M)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.prop.1.2) ⊤) :
    M.subgroupOf H = ChapterB.minimalParabolicMax (T.subtype hH.prop.1.2) hP := by
  let A := ChapterB.minimalParabolicMax (T.subtype hH.prop.1.2) hP
  have hA := ChapterB.minimalParabolicMax_spec (T.subtype hH.prop.1.2) hP
  have hTH : (T : Subgroup G) ≤ H := hH.prop.1.2
  have hTA : (T : Subgroup G) ≤ A.map H.subtype := by
    have hh := map_mono (f := H.subtype) hA.2
    change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ A.map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTH] at hh
  have hQA : H.pCoreIn 2 ≤ A.map H.subtype := by
    have hh := pCoreIn_le_sylow H (T.subtype hTH)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rw [map_subgroupOf_eq_of_le hTH] at hh
    exact hh.trans hTA
  have hAM : A.map H.subtype ≤ M := by
    by_contra hnot
    have hAcore : (A.map H.subtype).pCoreIn 2 ≠ ⊥ := by
      intro he
      apply hH.prop.1.1
      apply eq_bot_iff.mpr
      calc H.pCoreIn 2 ≤ A.map H.subtype ⊓ H.pCoreIn 2 := le_inf hQA le_rfl
           _ ≤ (A.map H.subtype).pCoreIn 2 := inf_pCoreIn_le_of_le 2 (map_subtype_le A)
           _ = ⊥ := he
    have hHA := hH.le_of_le (show A.map H.subtype ∈ sylowOutsideFamily T M from
      ⟨⟨hAcore, hTA⟩, hnot⟩) (map_subtype_le A)
    have he : A = ⊤ := by
      apply map_subtype_inj.mp
      calc A.map H.subtype = H := le_antisymm (map_subtype_le A) hHA
           _ = (⊤ : Subgroup H).map H.subtype := by ext x; simp
    exact hA.1.ne_top he
  have hle : A ≤ M.subgroupOf H := map_le_iff_le_comap.mp hAM
  rcases hA.1.le_iff.mp hle with he | he
  · exact False.elim (hH.prop.2 (subgroupOf_eq_top.mp he))
  · exact he

/-- Consequently the two definitions of the source kernel agree. -/
theorem sourceKernel_eq_minimalParabolicCore
    {T : Sylow 2 G} {H M : Subgroup G}
    (hH : H ∈ minimalSylowOutsideFamily T M)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.prop.1.2) ⊤) :
    sourceKernel H M = ChapterB.minimalParabolicCore (T.subtype hH.prop.1.2) hP := by
  rw [sourceKernel, overlap_eq_minimalParabolicMax hH hP]
  rfl

/-- The canonical map H/O₂(H) → H/J has its genuine required containment. -/
theorem twoCore_le_sourceKernel
    {T : Sylow 2 G} {H M : Subgroup G}
    (hH : H ∈ minimalSylowOutsideFamily T M)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.prop.1.2) ⊤) :
    pCore 2 H ≤ sourceKernel H M := by
  rw [sourceKernel_eq_minimalParabolicCore hH hP]
  exact ChapterB.minimalParabolicTwoCore_le_core _ hP
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction.SourceCases
