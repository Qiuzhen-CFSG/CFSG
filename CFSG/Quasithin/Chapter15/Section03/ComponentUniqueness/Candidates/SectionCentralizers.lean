module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Basic

/-!
# The two centralizer conventions in the residual decomposition

15.3.12 uses `C_{Y₊}(L/O₂(L))`, whereas 15.3.37 uses `C_{Y₊}(L)`.
For a perfect subgroup whose two-core is central, the two centralizers
coincide. Indeed, `[[C,L],L] = 1`; the three-subgroup lemma and `L = [L,L]`
give `[C,L] = 1`. The converse follows directly from the definition of
the section centralizer. Taking the actual two-residual then gives the
required identity, without replacing either residual by a two-core.

The component-existence argument supplies `Z(L) = O₂(L)` for the chosen
ordinary component. No converse from C-components to ordinary components
is used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.12(2) and 15.3.37(2), printed pp.1125 and 1135.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G]

/-- A perfect subgroup with central two-core has no nontrivial
central automorphisms. Thus its section centralizer is its centralizer. -/
theorem sectionCentralizer_eq_centralizer_of_perfect {L : Subgroup G}
    [Group.IsPerfect L] (hcore : pCore 2 L ≤ center L) :
    Chapter4.sectionCentralizer L = centralizer (L : Set G) := by
  have hcoreC : L.pCoreIn 2 ≤ centralizer (L : Set G) := by
    rintro x ⟨a, ha, rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp (hcore ha) (⟨y, hy⟩ : L))
  have hc : ⁅Chapter4.sectionCentralizer L, L⁆ ≤ L.pCoreIn 2 :=
    commutator_commutatorPreimage_le _ _ _
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hcc : ⁅⁅Chapter4.sectionCentralizer L, L⁆, L⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hc.trans hcoreC)
  have hcc' : ⁅⁅L, Chapter4.sectionCentralizer L⁆, L⁆ = ⊥ := by
    rwa [commutator_comm L]
  have hL : ⁅⁅L, L⁆, Chapter4.sectionCentralizer L⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate hcc' hcc
  rw [commutator_eq_self, commutator_comm] at hL
  refine le_antisymm (commutator_eq_bot_iff_le_centralizer.mp hL) ?_
  apply le_commutatorPreimage (Subgroup.centralizer_le_normalizer _)
  exact (commutator_eq_bot_iff_le_centralizer.mpr le_rfl).le.trans bot_le

/-- The residual denoted Y_C in 15.3.12 agrees with the one in 15.3.37
once the component two-core has been proved central. -/
theorem sectionCentralizingPart_eq_centralizingPart {L Yplus : Subgroup G}
    [Group.IsPerfect L] (hcore : pCore 2 L ≤ center L) :
    sectionCentralizingPart Yplus L = centralizingPart Yplus L := by
  unfold sectionCentralizingPart centralizingPart Chapter4.sectionCentralizerIn
  rw [sectionCentralizer_eq_centralizer_of_perfect hcore]

/-- The ordinary component selected before 15.3.33 satisfies the condition
needed to transport the earlier residual decomposition. -/
theorem ordinary_component_sectionCentralizingPart [Finite G]
    {L Yplus : Subgroup G} (hL : IsComponent G L) (hodd : pPrimeCore 2 G = ⊥) :
    sectionCentralizingPart Yplus L = centralizingPart Yplus L := by
  let := hL.2
  exact sectionCentralizingPart_eq_centralizingPart (component_center_eq_twoCore hL hodd).ge

end CFSG.Quasithin.Chapter15.Section03
