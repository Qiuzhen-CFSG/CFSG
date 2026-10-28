module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesNatural
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesOpposite

/-!
# The opposite subgroup in the faithful centralizer-span action

The Cartan and local plane data construct the natural coordinates needed
by G.2.3. Its complementary natural summands show that the opposite
subgroup has kernel exactly S₂ on U/⟨z⟩. Factoring through the original
two-core quotient preserves its elementary image and the exact index
|U:S₂| = 2 |A*|. These are the literal groups and quotient maps in 5.1.23.

The multiplicity bound and cubic constituent obstruction are subsequent
steps; neither is assumed or asserted here.

Source: Aschbacher--Smith, G.2.3 and 5.1.23, printed pp.333--334,645.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
open ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H A B C : Subgroup G} {n : ℕ} {z : G}

/-- Some element of the original cubic moves the point. -/
theorem LocalData.exists_moving_cubic (d : LocalData T H C z) :
    ∃ g ∈ C, g ∉ normalizer (zpowers z : Set G) := by
  by_contra hn
  have hCN : C ≤ normalizer (zpowers z : Set G) := by
    intro g hg
    by_contra hh
    exact hn ⟨g, hg, hh⟩
  have he : plane C z = zpowers z := le_antisymm
    (conjugateSpanBy_le le_rfl hCN) (le_conjugateSpanBy _ _)
  have hc := d.plane_card
  rw [he, d.point_card] at hc
  omega


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
