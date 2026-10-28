module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.FullShortCentralizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FullLongCentralizers
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Native involution geometry on the exact U₅(4) marking

The reduced endpoint equivalence carries the canonical core center back to
Z(O₂(L)). Every native involution is conjugate, inside the same extension,
to the marked image of an original element of that center. The explicit
short involution pulls back through this identical endpoint map. Its entire
extension centralizer lies in the full plane endpoint, and its order equals
the original local centralizer inside N_G(L).

Both orientations remain admitted, with the impossible unreversed row
excluded by the prepared-source theorem. All endpoint and whole-overlap
equations and all four range equalities are retained. Native coverage does
not give ambient involution coverage. Equality of the original full ambient
short centralizer with its local subgroup still requires F.4.42.
Source: Aschbacher–Smith F.4.27(3–4), F.4.35 and F.4.42, pp.288,292,295.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem core_center_preimage {X : Type*} [Group X]
    {L P : Subgroup G} {R Q : Subgroup X} (hLP : L ≤ P) (e : P ≃* Q)
    (hR : (L.subgroupOf P).map (Q.subtype.comp e.toMonoidHom) = R)
    (y : Q) (hy : y.val ∈ (center (R.pCoreIn 2)).map (R.pCoreIn 2).subtype) :
    (e.symm y).val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype := by
  let f := Q.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hQ : ((L.pCoreIn 2).subgroupOf P).map f = R.pCoreIn 2 := by
    rw [←pCoreIn_subgroupOf 2 L P hLP,map_pCoreIn_of_injective 2 _ f hf,hR]
  have hQP : L.pCoreIn 2 ≤ P := (L.pCoreIn_le 2).trans hLP
  let eq : L.pCoreIn 2 ≃* R.pCoreIn 2 :=
    (subgroupOfEquivOfLe hQP).symm.trans
      ((((L.pCoreIn 2).subgroupOf P).equivMapOfInjective f hf).trans
        (MulEquiv.subgroupCongr hQ))
  obtain ⟨v,hv,he⟩ := hy
  let z := eq.symm v
  have hz : z ∈ center (L.pCoreIn 2) := (centerCongr eq.symm ⟨v,hv⟩).property
  have heq : f ⟨z.val,hQP z.property⟩ = y.val :=
    (congrArg Subtype.val (eq.apply_symm_apply v)).trans he
  have hzy : (⟨z.val,hQP z.property⟩ : P) = e.symm y := by
    apply e.injective
    apply Subtype.ext
    exact heq.trans (congrArg Subtype.val (e.apply_symm_apply y)).symm
  exact ⟨z,hz,congrArg Subtype.val hzy⟩

variable {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- Native involution coverage and the selected short-root centralizer bound,
transported on the exact published marking of the original prepared row. -/
theorem Preparation.unitaryFive_marked_native_involutions
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U) :
    ∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse,
    ∃ f : UnitaryNativeLift.Five.LiftReverse U a,
    ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
        r.extension.amalgam.reverse,
      (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
      (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
      (∀ z, (F.middle z).val = (f.action z).val) ∧
      r.extension.carrier = inner U.Carrier ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.left = U.leftParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.right = U.rightParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.middle =
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      (∀ u : U.Carrier, orderOf u = 2 →
        ∃ z : ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0,
          z.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ∧
          orderOf z.val = 2 ∧
          IsConj (r.extension.baseHom u)
            (inclusion r.extension.right_le (F.left (inclusion r.left_le z)))) ∧
      (∃ z : ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0,
        z.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ∧
        orderOf z.val = 2 ∧ a.comparison.left z = U.shortInvolution ∧
        centralizer ({inclusion r.extension.right_le (F.left (inclusion r.left_le z))} :
          Set r.extension.carrier) ≤ r.extension.right.subgroupOf r.extension.carrier ∧
        Nat.card (centralizer ({inclusion r.left_le z} : Set (normalizer (L : Set G)))) =
          Nat.card (centralizer ({inclusion r.extension.right_le (F.left (inclusion r.left_le z))} :
            Set r.extension.carrier))) := by
  have hs := d.unitaryFive_sourceS_eq h hH.1.1.2 hp U hc
  rcases r.marking with ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle⟩ |
    ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle⟩
  · exfalso
    apply d.not_unitaryFive_unreversed h hH.1.1.2 hp U
    rw [hs]
    exact ⟨a.comparison⟩
  · let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0
    have hLP : L ≤ P := le_sup_left.trans le_sup_left
    have hR : (L.subgroupOf P).map (U.rightParabolic.subtype.comp a.comparison.left.toMonoidHom) =
        U.rightLocalImage := by
      have hres : L.subgroupOf P = solvableResidual P := by
        have he : (solvableResidual P).map P.subtype = L :=
          d.reduced_parabolic_residuals h hH.1.1.2 hp (.unitaryFive U hc) 0
        rw [←he]
        exact comap_map_eq_self_of_injective P.subtype_injective _
      rw [hres,←map_map,map_solvableResidual_eq a.comparison.left.toMonoidHom
        a.comparison.left.surjective]
      rfl
    have hmark (y : U.rightParabolic) :
        inclusion r.extension.right_le (F.left (inclusion r.left_le (a.comparison.left.symm y))) =
          r.extension.baseHom y.val := by
      apply Subtype.ext
      change (F.left (inclusion r.left_le (a.comparison.left.symm y))).val = MulAut.conj y.val
      rw [h0,a.comparison.left.apply_symm_apply]
    have hord (y : U.rightParabolic) : orderOf (a.comparison.left.symm y).val = orderOf y := by
      rw [Subgroup.orderOf_coe,a.comparison.left.symm.orderOf_eq]
    refine ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle,?_,?_⟩
    · intro u hu
      obtain ⟨y,hy,hy2,huy⟩ := U.involution_to_right_core_center u hu
      refine ⟨a.comparison.left.symm y,core_center_preimage hLP a.comparison.left hR y hy,
        (hord y).trans hy2,?_⟩
      rw [hmark]
      exact r.extension.baseHom.map_isConj huy
    · refine ⟨a.comparison.left.symm U.shortInvolution,
        core_center_preimage hLP a.comparison.left hR _ U.shortInvolution_mem_center,
        (hord _).trans U.shortInvolution_order,a.comparison.left.apply_symm_apply _,?_⟩
      have hfull : centralizer
          ({inclusion r.extension.right_le (F.left (inclusion r.left_le
            (a.comparison.left.symm U.shortInvolution)))} : Set r.extension.carrier) ≤
          r.extension.right.subgroupOf r.extension.carrier := by
        rw [hmark]
        exact FiveExtension.shortInvolution_centralizer_le U r.extension
      refine ⟨hfull,?_⟩
      let z := inclusion r.left_le (a.comparison.left.symm U.shortInvolution)
      let e := (subgroupOfEquivOfLe r.extension.right_le).symm
      exact (Nat.card_congr (CentralizerSmallKernelTransport.centralizerEquiv F.left z).toEquiv).trans
        ((Nat.card_congr (CentralizerSmallKernelTransport.centralizerEquiv e (F.left z)).toEquiv).trans
          (Nat.card_congr (TwoInvolutionClassOrder.centralizerEquiv
            (r.extension.right.subgroupOf r.extension.carrier) (e (F.left z)) hfull)))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
