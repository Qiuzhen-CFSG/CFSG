module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson.OriginalAction
public import CFSG.Quasithin.ChapterB.InternalThompsonFixedSpace
public import Theory.Representation.BinaryOffender.MarkedCentralQuotient
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# Faithful descent through the original central part

The original Irr+ condition supplies V=[V,L]. The quotient projection has
kernel exactly the fixed space of the marked L-image. Its induced action
on that image is the supplied faithful L/O2(L) action. The general
fixed-quotient faithfulness theorem therefore applies to the entire
original actor. Fixed codimension can only decrease on this quotient,
so each original offender remains an offender, even for a nonsplit
central attachment.

This discharges the quotient and offender transport in the natural-module
Thompson argument of Aschbacher--Smith 11.4.2, printed p.777, using B.2.5
and the original Irr+ choice of A.1.40.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (S : D.NonbinaryNaturalInput)

def sourceLinearEquiv : Additive (originalModule S) ≃ₗ[ZMod 2] D.space :=
  let e : originalModule S ≃* Multiplicative D.space :=
    (subgroupOfEquivOfLe (D.le_sylow.trans
      (le_sup_right : (T : Subgroup G) ≤ originalGroup D))).trans D.spaceEquiv.symm
  let a : Additive (originalModule S) ≃+ D.space := {
    toFun v := (e v.toMul).toAdd
    invFun w := Additive.ofMul (e.symm (Multiplicative.ofAdd w))
    left_inv v := e.symm_apply_apply v.toMul
    right_inv w := e.apply_symm_apply (Multiplicative.ofAdd w)
    map_add' v w := e.map_mul v.toMul w.toMul }
  a.toLinearEquiv (ZMod.map_smul a)

theorem sourceLinearEquiv_val (v : Additive (originalModule S)) :
    ((sourceLinearEquiv S v).val.toMul.val : G) = ((v.toMul : originalGroup D) : G) := by
  rw [← D.spaceEquiv_apply]
  change (D.spaceEquiv (D.spaceEquiv.symm _)).val = _
  rw [D.spaceEquiv.apply_symm_apply]
  rfl

theorem sourceLinearEquiv_component (l : L) (v : Additive (originalModule S)) :
    sourceLinearEquiv S (originalAction S (layerProjection S l) v) =
      D.chosenAction l (sourceLinearEquiv S v) := by
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  change ((sourceLinearEquiv S (originalAction S (layerProjection S l) v)).val.toMul.val : G) =
    (l : G) * ((sourceLinearEquiv S v).val.toMul.val : G) * (l : G)⁻¹
  rw [sourceLinearEquiv_val, sourceLinearEquiv_val]
  exact congrArg (fun x : originalGroup D => (x : G))
    (ChapterB.InternalThompsonAction.action_apply (originalModule S)
      ⟨l,(le_sup_left : L ≤ originalGroup D) l.property⟩ v)

theorem originalAction_generated :
    subspaceCommutator (originalAction S) ⊤ (originalLayer S) = ⊤ := by
  let U := subspaceCommutator (originalAction S) ⊤ (originalLayer S)
  have hle : D.space ≤ (U.map (sourceLinearEquiv S).toLinearMap).map D.space.subtype := by
    apply D.irrPlus.isIrrPlus.choose_spec.1.ge.trans
    apply Submodule.span_le.mpr
    rintro _ ⟨l,hl,v,hv,rfl⟩
    let l' : L := ⟨l.val,hl⟩
    let w : D.space := ⟨v,hv⟩
    refine ⟨D.chosenAction l' w - w, ?_, rfl⟩
    refine ⟨originalAction S (layerProjection S l') ((sourceLinearEquiv S).symm w) -
      (sourceLinearEquiv S).symm w, ?_, ?_⟩
    · exact Submodule.subset_span ⟨layerProjection S l', (layerProjection S l').property,
        (sourceLinearEquiv S).symm w, Submodule.mem_top, rfl⟩
    · rw [map_sub]
      change sourceLinearEquiv S (originalAction S (layerProjection S l')
        ((sourceLinearEquiv S).symm w)) - sourceLinearEquiv S ((sourceLinearEquiv S).symm w) = _
      rw [sourceLinearEquiv_component, LinearEquiv.apply_symm_apply]
  apply top_unique
  intro v _
  obtain ⟨w,⟨u,hu,heu⟩,hew⟩ := hle (sourceLinearEquiv S v).property
  have he : sourceLinearEquiv S u = sourceLinearEquiv S v := heu.trans (Subtype.ext hew)
  exact (sourceLinearEquiv S).injective he ▸ hu

theorem moduleProjection_ker :
    (moduleProjection S).ker = fixedSpace (originalAction S) (originalLayer S) := by
  ext v
  change D.toCentralQuotient ((subgroupOfEquivOfLe
    (D.le_sylow.trans (le_sup_right : (T : Subgroup G) ≤ originalGroup D))) v.toMul) = 1 ↔ _
  rw [LocalGeometry.quotient_eq_one_iff]
  change _ ↔ v ∈ fixedSpace (ChapterB.InternalThompsonAction.action (originalModule S))
    ((L.subgroupOf (originalGroup D)).map (originalProjection S))
  rw [ChapterB.InternalThompsonAction.mem_fixedSpace_iff]
  constructor
  · intro h l hl
    exact Subtype.ext (h l hl)
  · intro h l hl
    exact congrArg (fun x : originalGroup D => (x : G))
      (h ⟨l,(le_sup_left : L ≤ originalGroup D) hl⟩ hl)

abbrev CentralActionSpace := Additive (originalModule S) ⧸
  fixedSpace (originalAction S) (originalLayer S)
def centralAction : Representation (ZMod 2) (OriginalQuotient S) (CentralActionSpace S) :=
  fixedQuotient (originalAction S) (originalLayer S)

def centralEquiv : CentralActionSpace S ≃ₗ[ZMod 2] D.chosenCentralQuotient :=
  (Submodule.quotEquivOfEq _ _ (moduleProjection_ker S).symm).trans
    ((moduleProjection S).quotKerEquivOfSurjective (moduleProjection_surjective S))

theorem centralEquiv_mk (v : Additive (originalModule S)) :
    centralEquiv S (Submodule.Quotient.mk v) = moduleProjection S v := rfl

def centralActionEquiv : ChapterB.QuasisimpleSource.ActionEquiv
    ((centralAction S).comp (originalLayer S).subtype) D.centralQuotientAction where
  groupEquiv := (layerEquiv S).symm
  linearEquiv := centralEquiv S
  intertwines g v := by
    obtain ⟨l,rfl⟩ := layerProjection_surjective S g
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      change centralEquiv S (Submodule.Quotient.mk (originalAction S (layerProjection S l) v)) = _
      rw [centralEquiv_mk]
      have hg : (layerEquiv S).symm (layerProjection S l) =
          QuotientGroup.mk' (pCore 2 L) l := by
        rw [← layerEquiv_mk, MulEquiv.symm_apply_apply]
      rw [hg]
      exact moduleProjection_component S l v

theorem centralAction_faithful : Function.Injective (centralAction S) := by
  apply fixedQuotient_faithful (originalAction S) (originalLayer S)
    (ChapterB.InternalThompsonAction.action_faithful _) ?_ (originalAction_generated S)
  intro a b hab
  apply (layerEquiv S).symm.injective
  apply S.faithful
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := (centralEquiv S).surjective v
  calc
    _ = centralEquiv S (centralAction S a w) := ((centralActionEquiv S).intertwines a w).symm
    _ = centralEquiv S (centralAction S b w) :=
      congrArg (centralEquiv S) (LinearMap.congr_fun hab w)
    _ = _ := (centralActionEquiv S).intertwines b w

theorem original_offender_on_central {A : Subgroup (OriginalQuotient S)}
    (hA : IsOffender (originalAction S) A) : IsOffender (centralAction S) A := by
  refine ⟨hA.1, ?_⟩
  have h := fixedCodim_quotient_add_subrepresentation_le (originalAction S)
    (fixedSubrepresentation (originalAction S) (originalLayer S)) A
  exact (Nat.le_add_right _ _).trans (h.trans hA.2)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson
