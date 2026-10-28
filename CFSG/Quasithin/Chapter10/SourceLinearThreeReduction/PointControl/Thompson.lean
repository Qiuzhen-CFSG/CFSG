module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfSylow

/-!
# The centralizing-Thompson branch of non-A₅ point preparation

If J(T) centralizes the full module, the guarded common-normal theorem
annihilates its L₀-fixed layer. Every nonzero opposite moved vector
therefore distinguishes the two components. The original pair action
forces its Sylow centralizer to normalize L, and Thompson control puts
the normalizer of that Sylow centralizer in M.

This proves the whole point-Sylow preparation in this branch, without a
module model, an A₅ marking, or half-Sylow uniqueness. The remaining
chosen-module producer only needs the moving-Thompson branch after
constructing crossed centralization.
Source: Aschbacher--Smith, 3.2.10(8--9) and the first paragraph of the
proof of 10.2.9, printed pp.583--584 and750.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual centralizing-Thompson case supplies both point-Sylow
conditions, including the component stabilizer. -/
theorem pointSylowControl_of_thompson_centralizes
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)) :
    PointSylowControl D t := by
  have hJlocal := hJ.trans (centralizer_le (le_componentOrbit D.moduleSubgroup D.maximalLocal))
  have hfix := source_fullModule_fixed_eq_bot_of_many D hmany hJlocal
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  intro v hv hvne _ _
  have hvV := partner_le_fullModule D ht hv
  have hv0 : v ∉ centralizer (localOrbit T L : Set G) := by
    intro hc
    exact hvne (mem_bot.mp (hfix ▸ (show v ∈ D.fullModule ⊓
      centralizer (localOrbit T L : Set G) from ⟨hvV,hc⟩)))
  refine ⟨source_element_sylow_normalizer_of_thompson_centralizes D hJ hvV,?_⟩
  exact (inf_le_inf (le_normalizer_componentOrbit L T) le_rfl).trans
    (source_nonnormal_element_centralizer_stabilizes D hn (hcross hv) hv0)

end CFSG.Quasithin.Chapter10.PointControl
