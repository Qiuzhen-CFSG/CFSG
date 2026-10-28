module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.LocalReduction.LocalAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.LocalReduction.FixedGeometry
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Index
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.Intersections
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosureCommutation

/-!
# Excluding zero corank on the original natural module

If Vˣ lies in M, its moved factor is the whole offender intersection.
Normalization and the common fixed space would give moduleA at least three
for a noncentralizing factor, whereas the full natural automizer has parameter
at most two. Thus every such factor centralizes W; the literal four-conjugator
argument gives [V,Vˣ]=1. Applied to the original attained offender this excludes
zero corank and permits E.3.25's reverse-normalizer conclusion.

The component-normalizer input belongs to source 10.2.6. All local action,
displacement, and zero-corank steps are discharged here; the remaining
positive-fixed-part and terminal TI steps stay with the small-offender owner.
Source: Aschbacher--Smith 10.2.10--12, printed pp.753--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {g : G}

/-- The source intersection theorem uses the genuine natural quotient and
requires no later survivor or value of w. -/
theorem natural_outside_intersection
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {x : G} (hx : x ∉ D.maximalLocal) :
    ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom = ⊥ := by
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  exact SourceLinearThreeReplacement.Geometry.FixedSpaceTI.moved_inf_conjugate_eq_bot
    D m.quotient c.nonnormal t ht (m.crossed t ht htn) c.pointCentralizers hNL hx

/-- The natural zero-corank branch is impossible for the actual attained
noncommuting offender, with only the earlier component-normalizer bound. -/
theorem natural_corank_ne_zero
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) :
    subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≠ 0 := by
  intro hzero
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  let := source_full_moved_elementary D
  let W := ⁅D.fullModule,L⁆
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  apply c.noncommuting
  apply source_a5_small_conjugates_commute_of_moved_factor D c.nonnormal ht
    (m.crossed t ht htn) 0 ?_ g hzero.le
  intro x hx hxs
  let : IsElementaryAbelian 2 (D.fullModule.map (MulAut.conj x).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hxzero := Nat.eq_zero_of_le_zero hxs
  have hxM : D.fullModule.map (MulAut.conj x).toMonoidHom ≤ D.maximalLocal := by
    have he := subgroup_eq_of_corank_zero (show
      D.fullModule.map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal ≤
      D.fullModule.map (MulAut.conj x).toMonoidHom from inf_le_left) hxzero
    exact he ▸ inf_le_right
  have hPM := (map_mono hWV).trans hxM
  refine ⟨hPM,?_⟩
  by_cases hcomm : ⁅D.fullModule,D.fullModule.map (MulAut.conj x).toMonoidHom⁆ = ⊥
  · exact (map_mono hWV).trans
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
        (centralizer_le hWV))
  let cx : Configuration T D x :=
    ⟨c.many,c.minimal,c.nonnormal,c.notA5,c.pointCentralizers,hx,hcomm,
      by rw [c.attained,hzero,hxzero], by omega⟩
  obtain ⟨hAN,hfix⟩ := natural_offender_geometry cx m (by omega)
    (natural_outside_intersection c m hNL hx)
  have hcentral : W.map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal ≤
      centralizer (W : Set G) := by
    by_contra hactive
    have hlo := Recognition.offender_moduleA_lower D (m := 3) (k := 0)
      (by decide) (moved_fixed_quotient_card_ge_eight D) hxs hAN hactive hfix
    have hhi := local_moduleA_le_two m c.nonnormal
    have hbad : (3 : ℕ) ≤ 2 := by exact_mod_cast hlo.trans hhi
    omega
  simpa only [inf_of_le_left hPM] using hcentral

/-- Corank at most one is exactly one, and the original full module cannot
lie in the conjugate local group. This is the entry to the fixed-part branch. -/
theorem natural_corank_one_and_reverse_escape
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1) :
    subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) = 1 ∧
      ¬ D.fullModule ≤ D.maximalLocal.map (MulAut.conj g).toMonoidHom := by
  have hne := natural_corank_ne_zero c m hNL
  have hone : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) = 1 := by omega
  refine ⟨hone,?_⟩
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  have hw : 0 < globalW D.fullModule (T : Subgroup G) := by
    rw [c.attained,hone]
    exact (by decide : (0 : ℕ∞) < 1)
  intro hle
  have he := lemma_E_3_25 (source_fullModule_weakClosure_hypotheses D) hw g
  have hVN : D.fullModule ≤ normalizer
      (D.fullModule.map (MulAut.conj g).toMonoidHom : Set G) :=
    hle.trans ((map_mono D.maximalLocal_normalizes_fullModule).trans
      (D.fullModule.le_normalizer_map (MulAut.conj g).toMonoidHom))
  exact c.noncommuting (commutator_eq_bot_iff_le_centralizer.mpr (he.2.2.mpr hVN))

end CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
