module

public import Stellmacher.ElementaryAbelianMaxOrder
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# An elementary two-core containing the Thompson subgroup

An elementary subgroup between J(S) and S equals J(S): compare its order
with a maximum elementary subgroup of S. Consequently, if J(T) is normal
in an overgroup H of the ambient Sylow two-subgroup T and O₂(H) is elementary,
then J(T)=O₂(H), with the core mapped into the original ambient group.

Source application: Aschbacher–Smith 13.4.7(1ii) and 13.4.9, printed
pp.899 and906. Relative normality is sufficient; ambient normality is
neither asserted nor required.
-/

public section

namespace Stellmacher
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- An elementary overgroup of J(S) inside S equals J(S). -/
theorem elementaryAbelianMaxJ_eq_of_elementary_overgroup (S W : Subgroup G)
    (hJW : elementaryAbelianMaxJ S ≤ W) (hWS : W ≤ S)
    (hW : IsElementaryAbelian 2 W) : elementaryAbelianMaxJ S = W := by
  apply le_antisymm hJW
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty S
  apply le_sSup
  refine ⟨hWS, hW, ?_⟩
  intro B hBS hB
  exact (hA.2.2 B hBS hB).trans (card_le_of_le ((le_sSup hA).trans hJW))

/-- A normal Sylow Thompson subgroup equals an elementary local two-core. -/
theorem elementaryAbelianMaxJ_eq_pCoreIn (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (hn : H ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (hcore : IsElementaryAbelian 2 (H.pCoreIn 2)) :
    elementaryAbelianMaxJ (T : Subgroup G) = H.pCoreIn 2 := by
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ T :=
    sSup_le fun _ hA => hA.1
  apply elementaryAbelianMaxJ_eq_of_elementary_overgroup _ _
    (le_pCoreIn_of_normalizes (T.isPGroup'.to_le hJT) (hJT.trans hTH) hn) _ hcore
  have h := H.pCoreIn_le_sylow (T.subtype hTH)
  rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at h

end Stellmacher
