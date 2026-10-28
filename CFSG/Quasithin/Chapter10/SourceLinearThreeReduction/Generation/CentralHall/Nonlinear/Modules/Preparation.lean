module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.Contracts
public import CFSG.Quasithin.Chapter10.SourceA5NumericalComplete
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels

/-!
# Literal source inputs for nonlinear module recognition

The original component is a nonnormal C-component of M=N_G(L₀).
Apply 1.2.1(3) inside M and transport its model through the canonical
isomorphism from the intrinsic two-core quotient of L.subgroupOf M to
L/O₂(L). This retains all four source alternatives, including odd PSL₂
and J₁; it makes no module-recognition claim.

The actual H* and multiple-overgroup hypotheses supply the two original
cubic bounds. These facts are consumed by `Modules.Source` and are not
additional source assumptions in its assembly.
Source: Aschbacher--Smith 1.2.1(3), 3.1.6--8, 10.1.1,
printed pp.504,573--581,741.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The complete source catalogue on the literal quotient L/O₂(L). -/
theorem component_model
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Chapter1.Section02.NonnormalCComponentModel (L ⧸ pCore 2 L) := by
  let M := D.maximalLocal
  let A := L.subgroupOf M
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  have hlocal : IsSQTK KnownSimple.IsKnownSimple M :=
    D.simpleQTKE.twoLocal_sqtk (source_module_nonsolvable_uniqueness D).normalizer_maximal.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_,hlocal.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hlocal.stronglyQuasithin p hp ho)
  have hnot : ¬ A.Normal := fun ha =>
    hn (hTM.trans ((normal_subgroupOf_iff_le_normalizer hLM).mp ha))
  obtain ⟨_,hm⟩ := (Chapter1.Section02.proposition_1_2_1_three_index_knownSimple hQ
    D.component_in_maximalLocal).resolve_left hnot
  let e := subgroupOfEquivOfLe hLM
  let eqt := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  exact hm.of_mulEquiv eqt.symm

/-- Both guarded numerical source bounds, on their original actions. -/
theorem cubic_bounds {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    SourceLocalModuleCubicBound D ∧ SourceFullModuleCubicBound D :=
  ⟨source_localModule_cubic_bound_of_hstar D c.hstar,
    source_full_module_cubic_bound_of_many D c.many⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
