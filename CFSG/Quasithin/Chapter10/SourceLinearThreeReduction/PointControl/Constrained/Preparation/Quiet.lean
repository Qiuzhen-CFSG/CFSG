module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Thompson

/-!
# Thompson equality for the quiet full-module branch

The selected point belongs to a conjugate of the original moved subgroup,
hence to the full module normalized by the maximal local subgroup. If J(T)
centralizes that module, it fixes the point. Thompson heredity then gives
J(C_T(v)) = J(T). This is the quiet branch of Aschbacher–Smith 10.2.9,
printed p.751, used by the natural–dual and irreducible orbit preparations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- In the quiet full-module branch, the original Thompson subgroup fixes
v and hence lies in its point Sylow. -/
theorem Context.thompson_eq_of_fullModule_centralized (c : Context D t v I)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)) :
    elementaryAbelianMaxJ (pointSylow T v) = elementaryAbelianMaxJ (T : Subgroup G) := by
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hvV : v ∈ D.fullModule := by
    obtain ⟨w,hw,rfl⟩ := c.escaping.v_mem
    exact (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule
      (le_normalizer_componentOrbit L T c.escaping.t_mem)) w).mp (hWV hw)
  apply elementaryAbelianMaxJ_eq_of_intermediate _ _ ?_ inf_le_left
  apply le_inf (sSup_le fun _ hA => hA.1)
  intro j hj
  exact mem_centralizer_singleton_iff.mpr (hJ hj v hvV).symm

end CFSG.Quasithin.Chapter10.PointControl.Constrained
