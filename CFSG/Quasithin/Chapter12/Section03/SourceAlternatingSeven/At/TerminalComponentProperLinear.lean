module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperLinear
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentResidualProper

/-!
# TerminalComponentProperLinear at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalComponentProperLinear`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Representation

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 Section02.RecognitionSource ChapterB.QuasisimpleSource

open BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V Y W : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

private def modelCoordinates_at (E : ChosenModule T Y W) {n : ℕ}
    (f : W ≃* Multiplicative (Space n)) :
    letI := E.elementary; Additive W ≃ₗ[ZMod 2] Space n := by
  let := E.elementary
  exact f.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)

private def modelAction_at (E : ChosenModule T Y W)
    (hT : (T : Subgroup G) ≤ normalizer (W : Set G)) {n : ℕ}
    (f : W ≃* Multiplicative (Space n)) :
    (Y ⊔ (T : Subgroup G) : Subgroup G) →* LinearGroup n := by
  let := E.elementary
  exact (linearGroupCongr (modelCoordinates_at E f)).toMonoidHom.comp (chosenJoinLinearAction E hT)

omit [Finite G] in

private theorem modelAction_component_at (E : ChosenModule T Y W)
    (hT : (T : Subgroup G) ≤ normalizer (W : Set G)) {n : ℕ}
    (e : (Y ⧸ pCore 2 Y) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (f : W ≃* Multiplicative (Space n))
    (he : ∀ (y : Y) (w : W),
      ((f.symm (Multiplicative.ofAdd ((specialLinearNatural (k := ZMod 2) n)
        (e (QuotientGroup.mk' (pCore 2 Y) y)) (f w).toAdd))) : G) =
        (y : G) * (w : G) * (y : G)⁻¹)
    (y : Y) :
    modelAction_at E hT f (inclusion (show Y ≤ Y ⊔ (T : Subgroup G) from le_sup_left) y) =
      slEquivLinear n (e (QuotientGroup.mk' (pCore 2 Y) y)) := by
  let := E.elementary
  apply LinearEquiv.ext
  intro v
  let w := f.symm (Multiplicative.ofAdd v)
  have hh : f.symm (Multiplicative.ofAdd ((specialLinearNatural (k := ZMod 2) n)
      (e (QuotientGroup.mk' (pCore 2 Y) y)) (f w).toAdd)) =
      (chosenJoinLinearAction E hT (inclusion le_sup_left y) (Additive.ofMul w)).toMul :=
    Subtype.ext (he y w)
  have hh' := congrArg (fun z : W => (f z).toAdd) hh
  simp only [f.apply_symm_apply, w,
    specialLinearNatural_apply] at hh'
  exact hh'.symm

omit [Finite G] in

private theorem modelAction_surjective_twoKernel_at (E : ChosenModule T Y W)
    (hT : (T : Subgroup G) ≤ normalizer (W : Set G)) {n : ℕ}
    (e : (Y ⧸ pCore 2 Y) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (f : W ≃* Multiplicative (Space n))
    (he : ∀ (y : Y) (w : W),
      ((f.symm (Multiplicative.ofAdd ((specialLinearNatural (k := ZMod 2) n)
        (e (QuotientGroup.mk' (pCore 2 Y) y)) (f w).toAdd))) : G) =
        (y : G) * (w : G) * (y : G)⁻¹) :
    Function.Surjective (modelAction_at E hT f) ∧ IsPGroup 2 (modelAction_at E hT f).ker := by
  let J := Y ⊔ (T : Subgroup G)
  let C := Y.subgroupOf J
  let U := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let a := modelAction_at E hT f
  have ha := modelAction_component_at E hT e f he
  constructor
  · intro g
    obtain ⟨y,hy⟩ := ((slEquivLinear n).surjective.comp
      (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 Y)))) g
    exact ⟨inclusion le_sup_left y,(ha y).trans hy⟩
  · let : C.Normal := normal_subgroupOf_of_le_normalizer
      (sup_le Y.le_normalizer E.sylow_normalizes_component)
    have hg : C ⊔ (U : Subgroup J) = ⊤ := by
      apply map_injective J.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left]
      change Y ⊔ ((T : Subgroup G).subgroupOf J).map J.subtype = _
      rw [map_subgroupOf_eq_of_le le_sup_right,←MonoidHom.range_eq_map,range_subtype]
    apply a.kernel_isPGroup_of_normal_supplement C U U.isPGroup' hg
    let c : C ≃* Y := subgroupOfEquivOfLe le_sup_left
    have hk : (a.comp C.subtype).ker = (pCore 2 Y).comap c.toMonoidHom := by
      ext y
      change a y.val = 1 ↔ c y ∈ pCore 2 Y
      change modelAction_at E hT f (inclusion le_sup_left (c y)) = 1 ↔ _
      rw [ha,(slEquivLinear n).map_eq_one_iff,e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff (c y)
    rw [hk]
    exact pCore_isPGroup.comap_of_injective c.toMonoidHom c.injective

theorem proper_overcomponent_not_natural_linear_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hY : Y ∈ Chapter1.LStar G (T : Subgroup G))
    (hKY : P.K < Y) (E : ChosenModule T Y W) {n : ℕ} (hn : 0 < n) :
    ¬ Nonempty (ActionEquiv E.quotientAction (specialLinearNatural (k := ZMod 2) n)) := by
  rintro ⟨model⟩
  obtain ⟨e,f,he⟩ := E.conjugationModel_of_quotientAction model
  have hTW := ((structural Y
    (P.residual_overgroup_hypothesis_at structural modules hr hw hY hKY.le)).2.2 W E).1
  let J := Y ⊔ (T : Subgroup G)
  let U := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hHJ : P.H ≤ J := by
    rw [← P.residual_sup_sylow]
    exact sup_le_sup hKY.le le_rfl
  let B := P.H.subgroupOf J
  let c : B ≃* P.H := subgroupOfEquivOfLe hHJ
  have hUB : (U : Subgroup J) ≤ B := by
    intro t ht
    exact P.minimal.1.1.2 ht
  have hu := ((P.minimalParabolic_at structural hw).1).map c.symm.mapSubgroup
  have heU : ((T.subtype P.minimal.1.1.2 : Subgroup P.H)).map c.symm.toMonoidHom =
      (U : Subgroup J).subgroupOf B := by
    ext x
    rw [mem_map_equiv]
    rfl
  change Order.HasUniqueMaximalOver
    ((T.subtype P.minimal.1.1.2 : Subgroup P.H).map c.symm.toMonoidHom)
    ((⊤ : Subgroup P.H).map c.symm.toMonoidHom) at hu
  rw [heU,map_top_of_surjective _ c.symm.surjective] at hu
  obtain ⟨hs,hk⟩ := modelAction_surjective_twoKernel_at E hTW e f he
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let : Group.IsSolvable B :=
    BinaryLinear.SylowFlagOvergroups.solvable_of_two_kernel_uniqueMaximal
      (modelAction_at E hTW f) hs hk U B hUB hu
  exact P.not_solvable_at structural hr hw
    (Group.isSolvable_of_surjective (f := c.toMonoidHom) c.surjective)

/-- The proper-overcomponent rows after excluding every full natural action. -/
theorem proper_overcomponent_nonnatural_alternatives_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hY : Y ∈ Chapter1.LStar G (T : Subgroup G))
    (hKY : P.K < Y) (E : ChosenModule T Y W) :
    ProperOvercomponentNonnaturalAlternatives E := by
  cases P.proper_overcomponent_alternatives_at structural modules hr hw hY hKY E with
  | linear n hn action =>
    exact (P.proper_overcomponent_not_natural_linear_at structural modules hr hw hY hKY E
      (by omega : 0 < n) ⟨action⟩).elim
  | linearFiveExterior groupEquiv dimension irreducible =>
    exact .linearFiveExterior groupEquiv dimension irreducible
  | alternating n degree action => exact .alternating n degree action
  | alternatingSevenFour groupEquiv dimension => exact .alternatingSevenFour groupEquiv dimension

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

