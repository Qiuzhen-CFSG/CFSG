module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperExterior
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentProperLinear

/-!
# TerminalComponentProperExterior at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalComponentProperExterior`, with structural
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

open BinaryLinear.OuterCyclic

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V Y W : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

private theorem join_actor_of_self_normalizing_at
    {A M : Type*} [Group A] [AddCommGroup M] [Module (ZMod 2) M]
    (E : ChosenModule T Y W)
    (hT : (T : Subgroup G) ≤ normalizer (W : Set G))
    (σ : Representation (ZMod 2) A M) (hf : Function.Injective σ.asGroupHom)
    (hn : normalizer (σ.asGroupHom.range : Set (Module.End (ZMod 2) M)ˣ) = σ.asGroupHom.range)
    (model : ActionEquiv E.quotientAction σ) :
    ∃ a : (Y ⊔ (T : Subgroup G) : Subgroup G) →* A,
      Function.Surjective a ∧ IsPGroup 2 a.ker := by
  let := E.elementary
  obtain ⟨e,f,he⟩ := E.conjugationModel_of_quotientAction model
  let c : Additive W ≃ₗ[ZMod 2] M :=
    f.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)
  let J := Y ⊔ (T : Subgroup G)
  let τ : Representation (ZMod 2) J M :=
    c.conjRingEquiv.toMonoidHom.comp (chosenJoinAction E hT)
  have hres (y : Y) : τ.asGroupHom (inclusion (show Y ≤ J from le_sup_left) y) =
      σ.asGroupHom (e (QuotientGroup.mk' (pCore 2 Y) y)) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    let w := f.symm (Multiplicative.ofAdd v)
    have hh : f.symm (Multiplicative.ofAdd (σ (e (QuotientGroup.mk' (pCore 2 Y) y))
        (f w).toAdd)) =
        (chosenJoinAction E hT (inclusion le_sup_left y) (Additive.ofMul w)).toMul :=
      Subtype.ext (he y w)
    have hh' := congrArg (fun z : W => (f z).toAdd) hh
    simp only [f.apply_symm_apply, w] at hh'
    exact hh'.symm
  let C := Y.subgroupOf J
  let U := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Y.le_normalizer E.sylow_normalizes_component)
  have himg : C.map τ.asGroupHom = σ.asGroupHom.range := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨e (QuotientGroup.mk' (pCore 2 Y) ⟨y,hy⟩),(hres ⟨y,hy⟩).symm⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨q,rfl⟩ := e.surjective g
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 Y) q
      exact ⟨inclusion le_sup_left y,y.property,hres y⟩
  have hnorm := C.le_normalizer_map τ.asGroupHom
  rw [normalizer_eq_top,himg,hn] at hnorm
  let β : J →* σ.asGroupHom.range := τ.asGroupHom.codRestrict _
    (fun x => hnorm ⟨x,mem_top x,rfl⟩)
  let b := MonoidHom.ofInjective hf
  let a := b.symm.toMonoidHom.comp β
  have ha (y : Y) : a (inclusion (show Y ≤ J from le_sup_left) y) =
      e (QuotientGroup.mk' (pCore 2 Y) y) := by
    apply hf
    exact (congrArg Subtype.val (b.apply_symm_apply (β _))).trans (hres y)
  refine ⟨a,?_,?_⟩
  · intro g
    obtain ⟨q,rfl⟩ := e.surjective g
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 Y) q
    exact ⟨inclusion le_sup_left y,ha y⟩
  · have hg : C ⊔ (U : Subgroup J) = ⊤ := by
      apply map_injective J.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left]
      change Y ⊔ ((T : Subgroup G).subgroupOf J).map J.subtype = _
      rw [map_subgroupOf_eq_of_le le_sup_right,←MonoidHom.range_eq_map,range_subtype]
    apply a.kernel_isPGroup_of_normal_supplement C U U.isPGroup' hg
    let d : C ≃* Y := subgroupOfEquivOfLe le_sup_left
    have hk : (a.comp C.subtype).ker = (pCore 2 Y).comap d.toMonoidHom := by
      ext y
      change a (inclusion le_sup_left (d y)) = 1 ↔ d y ∈ pCore 2 Y
      rw [ha,e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff (d y)
    rw [hk]
    exact pCore_isPGroup.comap_of_injective d.toMonoidHom d.injective

private theorem not_binary_join_actor_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hKY : P.K ≤ Y) {m : ℕ}
    (a : (Y ⊔ (T : Subgroup G) : Subgroup G) →* LinearGroup (m+1))
    (hs : Function.Surjective a) (hk : IsPGroup 2 a.ker) : False := by
  let J := Y ⊔ (T : Subgroup G)
  let U := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hHJ : P.H ≤ J := by
    rw [← P.residual_sup_sylow]
    exact sup_le_sup hKY le_rfl
  let B := P.H.subgroupOf J
  let c : B ≃* P.H := subgroupOfEquivOfLe hHJ
  have hUB : (U : Subgroup J) ≤ B := fun _ ht => P.minimal.1.1.2 ht
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
  let : Group.IsSolvable B :=
    BinaryLinear.SylowFlagOvergroups.solvable_of_two_kernel_uniqueMaximal a hs hk U B hUB hu
  exact P.not_solvable_at structural hr hw
    (Group.isSolvable_of_surjective (f := c.toMonoidHom) c.surjective)

theorem proper_overcomponent_not_exterior_five_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hY : Y ∈ Chapter1.LStar G (T : Subgroup G))
    (hKY : P.K < Y) (E : ChosenModule T Y W)
    (e : (Y ⧸ pCore 2 Y) ≃* SL5TenDimensional.Group)
    (hd : Module.finrank (ZMod 2) E.space = 10)
    (hi : IsIrreducible E.quotientAction) : False := by
  let := hi
  obtain ⟨q,c,_,hc⟩ := SL5ExteriorSquare.square_coordinates_of_finrank_ten E.quotientAction e hd
  let model : ActionEquiv E.quotientAction (SL5TenDimensional.exteriorAction 2) := ⟨q,c,hc⟩
  have hTW := ((structural Y
    (P.residual_overgroup_hypothesis_at structural modules hr hw hY hKY.le)).2.2 W E).1
  obtain ⟨a,ha,hk⟩ := join_actor_of_self_normalizing_at E hTW _
    (SL5TenDimensional.ExteriorNormalizer.exteriorAction_injective 0)
    SL5TenDimensional.ExteriorNormalizer.normalizer_two model
  let b := (slEquivLinear 5).toMonoidHom.comp a
  apply P.not_binary_join_actor_at structural hr hw hKY.le b
    ((slEquivLinear 5).surjective.comp ha)
  rw [MonoidHom.ker_comp_of_injective _ _ (slEquivLinear 5).injective]
  exact hk

/-- The proper-overcomponent cases after every linear row is excluded. -/
theorem proper_overcomponent_alternating_alternatives_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hY : Y ∈ Chapter1.LStar G (T : Subgroup G))
    (hKY : P.K < Y) (E : ChosenModule T Y W) :
    ProperOvercomponentAlternatingAlternatives E := by
  cases P.proper_overcomponent_nonnatural_alternatives_at structural modules hr hw hY hKY E with
  | linearFiveExterior e hd hi =>
    exact (P.proper_overcomponent_not_exterior_five_at structural modules hr hw hY hKY E e hd hi).elim
  | alternating n hn action => exact .alternating n hn action
  | alternatingSevenFour e hd => exact .alternatingSevenFour e hd

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

