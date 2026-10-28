module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Plane
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.TerminalConstruction.InnerAction
public import Theory.GroupTheory.PCoreQuotientInnerJoin
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.SpecificGroups.Janko4.Model.Center

/-!
# The full point-component join quotient in degree five

For each larger point model, the original Sylow subgroup acts innerly on
J/O₂(J). In the binary-linear case, conjugacy of a seven-element in the
original natural point residual excludes the graph automorphism; for M₂₄
and J₄, every automorphism is inner. The quotient of JT by its own two-core
is therefore isomorphic to J/O₂(J), with the same three model alternatives.
The same argument identifies L₁T/O₂(L₁T) with PSL₄(2), without requiring
normality of L₁ in the entire point normalizer.

This discharges the whole-group model premise for the literal quotient
obstruction constructed in Components/Overgroups. The finite-model subgroup
comparison remains with qt-d-1291-natural-source.
Source: Aschbacher--Smith, 12.9.3, printed pp.858--859 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem center_transfer {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hy : center Y = ⊥) : center X = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hm : e x ∈ center Y := (centerCongr e ⟨x,hx⟩).property
  rw [hy,mem_bot] at hm
  exact mem_bot.mpr (e.map_eq_one_iff.mp hm)

private theorem all_inner_transfer {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hy : Function.Surjective (MulAut.conj : Y →* MulAut Y))
    (a : MulAut X) : a ∈ MulAut.innerSubgroup X := by
  obtain ⟨y,hy⟩ := hy (MulAut.congr e a)
  refine ⟨e.symm y,?_⟩
  apply (MulAut.congr e).injective
  rw [MulAut.congr_conj,e.apply_symm_apply]
  exact hy

private theorem five_point_inner_action
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (J : Subgroup G)
    (hJH : J ≤ F.H) (hLJ : F.Li L 1 ≤ J)
    (hJn : (J.subgroupOf F.H).Normal)
    (hm : LargePointModel (J ⧸ pCore 2 J)) :
    let hn : (T : Subgroup G) ≤ normalizer (J : Set G) :=
      (F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer hJH).mp hJn)
    center (J ⧸ pCore 2 J) = ⊥ ∧
      ∀ t : T, pCoreJoinAction 2 hn (inclusion le_sup_right t) ∈
        MulAut.innerSubgroup (J ⧸ pCore 2 J) := by
  rcases hm with hb | hb | hb
  · have hi := binary_containing_point_sylow_acts_inner h (Or.inr rfl) earlier F J hJH hLJ hJn
      (Or.inr rfl) hb
    obtain ⟨k,hk,hfin,hcard,⟨e₀⟩⟩ := hb
    let ek := Theory.SpecificGroups.SymplecticSix.fieldEquivZModTwo k hcard
    let e := ((e₀.trans (Atlas.fieldEquivPSL 5 ek)).trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5))).trans
      (BinaryLinear.OuterCyclic.slEquivLinear 5).symm
    refine ⟨center_transfer e (BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide)),?_⟩
    exact hi
  · obtain ⟨e⟩ := hb
    exact ⟨center_transfer e Sporadic.Mathieu.M24InvolutionCentralizers.center_eq_bot,
      fun t => all_inner_transfer e Sporadic.Mathieu.M24OuterRestriction.conj_surjective _⟩
  · obtain ⟨e⟩ := hb
    exact ⟨center_transfer e Janko4.model_center_eq_bot,
      fun t => all_inner_transfer e Janko4.AdequateLocal.conj_surjective _⟩

/-- The full source point quotient equals its component image: the Sylow
acts innerly in all three larger degree-five models. -/
theorem five_point_join_quotient_model
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (J : Subgroup G)
    (hJH : J ≤ F.H) (hLJ : F.Li L 1 ≤ J)
    (hJn : (J.subgroupOf F.H).Normal)
    (hm : LargePointModel (J ⧸ pCore 2 J)) :
    Nonempty (((J ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G)) ≃* (J ⧸ pCore 2 J)) ∧
    LargePointModel (((J ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G))) := by
  have hn : (T : Subgroup G) ≤ normalizer (J : Set G) :=
    (F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer hJH).mp hJn)
  have hh := five_point_inner_action h earlier F J hJH hLJ hJn hm
  let e := pCoreJoinQuotientEquivOfInner J (T : Subgroup G) hn T.isPGroup' hh.1 hh.2
  refine ⟨⟨e⟩,?_⟩
  rcases hm with hb | hb | hb
  · exact Or.inl (hb.of_mulEquiv e)
  · obtain ⟨a⟩ := hb
    exact Or.inr (Or.inl ⟨e.trans a⟩)
  · obtain ⟨a⟩ := hb
    exact Or.inr (Or.inr ⟨e.trans a⟩)

/-- The image of the original point component is the whole literal join quotient. -/
theorem five_point_image_eq_top
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (J : Subgroup G)
    (hJH : J ≤ F.H) (hLJ : F.Li L 1 ≤ J)
    (hJn : (J.subgroupOf F.H).Normal)
    (hm : LargePointModel (J ⧸ pCore 2 J)) :
    (J.subgroupOf (J ⊔ (T : Subgroup G))).map
      (QuotientGroup.mk' (pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G))) = ⊤ := by
  have hn : (T : Subgroup G) ≤ normalizer (J : Set G) :=
    (F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer hJH).mp hJn)
  have hh := five_point_inner_action h earlier F J hJH hLJ hJn hm
  exact map_subgroupOf_pCoreJoin_eq_top_of_inner J (T : Subgroup G) hn T.isPGroup' hh.1 hh.2

/-- The original L₁T has the literal PSL₄(2) two-core quotient in degree five. -/
theorem five_point_residual_join_model
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) :
    ClassicalGroup.IsPSL ((F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)) 4 2 := by
  have hm : ClassicalGroup.IsPSL (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) 4 2 :=
    Li_core_model h F 1 (Or.inl ⟨rfl,by decide,by decide⟩)
  have hn := sylow_normalizes_point_residual h earlier F
  have hi := binary_normalized_point_overgroup_sylow_acts_inner h (Or.inr rfl) earlier F
    (F.Li L 1) le_rfl hn (Or.inl rfl) hm
  have hz : center (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) = ⊥ := by
    obtain ⟨k,hk,hfin,hcard,⟨e₀⟩⟩ := hm
    let ek := Theory.SpecificGroups.SymplecticSix.fieldEquivZModTwo k hcard
    let e := ((e₀.trans (Atlas.fieldEquivPSL 4 ek)).trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4))).trans
      (BinaryLinear.OuterCyclic.slEquivLinear 4).symm
    exact center_transfer e (BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide))
  let e := pCoreJoinQuotientEquivOfInner (F.Li L 1) (T : Subgroup G) hn T.isPGroup' hz hi
  exact hm.of_mulEquiv e

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
