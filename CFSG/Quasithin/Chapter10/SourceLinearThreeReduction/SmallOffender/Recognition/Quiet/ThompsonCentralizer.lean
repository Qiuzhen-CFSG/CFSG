module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.ThompsonComparison
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.PerfectCentralizer

/-!
# The full Thompson action and the orbit centralizer

A maximal elementary subgroup moving the full module maps to an actual
FF-offender. If Thompson fixes the local module, the local kernel comparison
puts this offender in the centralizer of the original component-orbit image.
The multiple-overgroup hypothesis kills the fixed space of that perfect image.
Glauberman's rank-one theorem then excludes a solvable orbit centralizer.

Quiet.SuzukiCentralizer applies the result to the fully moved Suzuki branch
and the literal small-offender contract. No tensor exclusion or module marking
is assumed. Source: Aschbacher--Smith B.1.8, 3.2.2(6), 10.1.1--2 and 10.2.12,
printed pp.70,579,741--742,754--755.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Full Thompson movement in the locally quiet branch produces an offender
in the literal orbit centralizer, with its inherited full-module action. -/
theorem full_orbit_centralizer_ff_of_local_quiet
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hmoves : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let X := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    let C := centralizer (X : Set (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)))
    IsFFModule ((ChapterB.InternalThompsonAction.action U).comp C.subtype) := by
  dsimp only
  by_contra hno
  apply hmoves
  let M := D.maximalLocal
  let R := localOrbit T L
  let H := localJoin T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let Q := M ⧸ centralizer (U : Set M)
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let X := (R.subgroupOf M).map q
  let C := centralizer (X : Set Q)
  let S := D.ambientSylow
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup M)).map M.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective]
    exact congrArg elementaryAbelianMaxJ
      (map_subgroupOf_eq_of_le (le_normalizer_componentOrbit L T))
  have hJC : (elementaryAbelianMaxJ (S : Subgroup M)).map q ≤ C := by
    rintro _ ⟨j,hj,rfl⟩
    have hjG : (j : G) ∈ elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [←hJmap]
      exact mem_map_of_mem M.subtype hj
    have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
      sSup_le fun _ hA => hA.1
    have hjT : (j : G) ∈ (T : Subgroup G) := hJT hjG
    have hjH : (j : G) ∈ H := (show (T : Subgroup G) ≤ H from le_sup_right) hjT
    apply ModuleChoice.local_kernel_full_image_le_centralizer D hn (⟨j,hjH⟩ : H)
    intro v hv
    exact Subtype.ext (hJ hjG v hv)
  have hfix : elementaryAbelianMaxJ (S : Subgroup M) ≤ centralizer (U : Set M) := by
    apply sSup_le
    intro E hE
    by_contra hEC
    have hn' : ¬ E ≤ q.ker := by
      simpa only [q,ChapterB.InternalThompsonAction.actionMk,QuotientGroup.ker_mk'] using hEC
    have hEU : U ≤ (S : Subgroup M) :=
      (IsElementaryAbelian.isPGroup 2 U).le_sylow_of_normal S
    have he : IsOffender ρ (E.map q) :=
      NormalElementaryQuotient.maxElementary_isOffender U q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
        (S : Subgroup M) E hEU hE hn'
    have hEC' : E.map q ≤ C := (map_mono (le_sSup hE)).trans hJC
    exact hno ⟨(E.map q).subgroupOf C,he.subgroupOf ρ hEC'⟩
  rw [←hJmap]
  rintro _ ⟨x,hx,rfl⟩ v hv
  have hVM : D.fullModule ≤ M := D.fullModule_le_orbit.trans R.le_normalizer
  exact congrArg M.subtype (hfix hx ⟨v,hVM hv⟩ hv)

/-- A solvable orbit centralizer extends local Thompson centralization to the full module. -/
theorem full_thompson_centralizes_of_local_solvable
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hsolv : let U := D.fullModule.subgroupOf D.maximalLocal
      let := (source_full_module_reduced D).normal
      let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
      let X := ((localOrbit T L).subgroupOf D.maximalLocal).map q
      Group.IsSolvable (centralizer (X : Set
        (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))))) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) := by
  let M := D.maximalLocal
  let R := localOrbit T L
  let H := localJoin T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let Q := M ⧸ centralizer (U : Set M)
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let X := (R.subgroupOf M).map q
  let C := centralizer (X : Set Q)
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : X.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : C.Normal := inferInstance
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect R := isPerfect_iSup_conjugates L T
  let : Group.IsPerfect (R.subgroupOf M) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe R.le_normalizer).symm.toMonoidHom)
      (subgroupOfEquivOfLe R.le_normalizer).symm.surjective
  let : Group.IsPerfect X := Group.IsPerfect.map q
  have hfixX : fixedSpace ρ X = ⊥ := by
    apply bot_unique
    intro v hv
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    apply (source_fullModule_fixed_eq_bot_of_many D hmany hJ).le
    refine ⟨v.toMul.property,?_⟩
    intro r hr
    let rM : M := ⟨r,R.le_normalizer hr⟩
    have hh := hv ⟨q rM,mem_map_of_mem q hr⟩
    have hact := ChapterB.InternalThompsonAction.action_apply U rM v
    have he : r * (v.toMul : G) * r⁻¹ = (v.toMul : G) := by
      exact (congrArg (fun x : M => (x : G)) hact).symm.trans
        (congrArg (fun x : Additive U => ((x.toMul : M) : G)) hh)
    exact mul_inv_eq_iff_eq_mul.mp he
  have hno : ¬ IsFFModule (ρ.comp C.subtype) :=
    ChapterB.noFF_of_solvable_commuting_perfect ρ (ChapterB.InternalThompsonAction.action_faithful U) X C
      hfixX hsolv (normal_subgroup_twoCore_eq_bot C hu.quotient_pCore_eq_bot) le_rfl
  by_contra hmoves
  exact hno (full_orbit_centralizer_ff_of_local_quiet D hn hJ hmoves)

/-- In the presence of full movement, the actual orbit centralizer is nonsolvable. -/
theorem full_orbit_centralizer_not_solvable_of_local_quiet
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hmoves : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let X := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    let C := centralizer (X : Set (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)))
    ¬ Group.IsSolvable C := by
  dsimp only
  intro hs
  exact hmoves (full_thompson_centralizes_of_local_solvable D hmany hn hJ hs)

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
