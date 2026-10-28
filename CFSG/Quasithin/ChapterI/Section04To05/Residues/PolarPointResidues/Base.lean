module
public import Theory.GroupAction.SurjectiveFlagCosets
public import Theory.SpecificGroups.SymmetricSix.Parabolics.PolarOrientation
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.StandardMarking
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.PointedCosets

/-!
# The original C₃ point stabilizer and its polar residue

The A₆/S₆ quotient marking identifies the two actual parabolic coset spaces
with the binary symplectic quadrangle, retaining either possible orientation.
Surjective coset transport preserves both incidence and the original action.
Source: Aschbacher–Smith, I.5.4 and I.5.9, pp.420–422.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
open Theory.SpecificGroups.SymmetricSix
namespace PolarPointResidues
variable {G : Type*} [Group G] (S : DSystem .C3 G)

structure BaseMark (dual : Bool) where
  actor : S.family 0 →* S6
  actor_ker : actor.ker=pCore 2 (S.family 0)
  actor_range : actor.range=A6 ∨ actor.range=⊤
  lines : PolarOrientation.Point dual ≃ {l : S.Line // S.Inc S.basePoint l}
  planes : PolarOrientation.Line dual ≃ {π : S.Plane // S.Inc S.basePoint π}
  incident : ∀ p l, S.Inc (lines p).val (planes l).val ↔ PolarOrientation.Inc dual p l
  lines_smul : ∀ (a : S.family 0) p, (lines (actor a • p)).val=(a:G) • (lines p).val
  planes_smul : ∀ (a : S.family 0) l, (planes (actor a • l)).val=(a:G) • (planes l).val

private theorem baseMark_of_quotient {K : Type*} [Group K] (dual : Bool)
    [MulAction K (PolarOrientation.Point dual)] [MulAction.IsPretransitive K (PolarOrientation.Point dual)]
    [MulAction K (PolarOrientation.Line dual)] [MulAction.IsPretransitive K (PolarOrientation.Line dual)]
    (f : S.family 0 →* K) (hf : Function.Surjective f) (hker : f.ker=pCore 2 (S.family 0))
    (hkP : f.ker≤localParabolic S.family 0 1) (hkL : f.ker≤localParabolic S.family 0 2)
    (j : K →* S6) (hj : Function.Injective j) (hrange : j.range=A6 ∨ j.range=⊤)
    (hpoint : ∀ (g : K) (p : PolarOrientation.Point dual), j g • p=g • p) (hline : ∀ (g : K) (l : PolarOrientation.Line dual), j g • l=g • l)
    (hP : (localParabolic S.family 0 1).map f=MulAction.stabilizer K (PolarOrientation.basePoint dual))
    (hL : (localParabolic S.family 0 2).map f=MulAction.stabilizer K (PolarOrientation.baseLine dual))
    (hflag : ∀ p l, PolarOrientation.Inc dual p l → ∃ g : K,
      g • PolarOrientation.basePoint dual=p ∧ g • PolarOrientation.baseLine dual=l) :
    Nonempty (BaseMark S dual) := by
  let ep := MulAction.surjectiveCosetEquiv (localParabolic S.family 0 1) f hf hkP
    (PolarOrientation.basePoint dual) hP
  let el := MulAction.surjectiveCosetEquiv (localParabolic S.family 0 2) f hf hkL
    (PolarOrientation.baseLine dual) hL
  let cp := S.pointedCosetEquiv 0 1 (by decide)
  let cl := S.pointedCosetEquiv 0 2 (by decide)
  have hpact (a : S.family 0) p : ep.symm (f a • p)=a • ep.symm p := by
    apply ep.injective
    rw [Equiv.apply_symm_apply]
    symm
    exact (MulAction.surjectiveCosetEquiv_smul _ f hf hkP _ hP a (ep.symm p)).trans
      (congrArg (fun p=>f a • p) (ep.apply_symm_apply p))
  have hlact (a : S.family 0) l : el.symm (f a • l)=a • el.symm l := by
    apply el.injective
    rw [Equiv.apply_symm_apply]
    symm
    exact (MulAction.surjectiveCosetEquiv_smul _ f hf hkL _ hL a (el.symm l)).trans
      (congrArg (fun l=>f a • l) (el.apply_symm_apply l))
  refine ⟨{ actor := j.comp f
            actor_ker := (MonoidHom.ker_comp_of_injective f j hj).trans hker
            actor_range := ?_
            lines := ep.symm.trans cp
            planes := el.symm.trans cl
            incident := ?_
            lines_smul := ?_
            planes_smul := ?_ }⟩
  · rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hf,←MonoidHom.range_eq_map]
    exact hrange
  · intro p l
    change S.Inc (S.pointedCosetEquiv 0 1 _ (ep.symm p)).val
      (S.pointedCosetEquiv 0 2 _ (el.symm l)).val ↔ _
    rw [←S.pointedCosetEquiv_incident 0 1 2]
    have hh := MulAction.surjectiveCosetEquiv_incident _ _ f hf hkP hkL
      (PolarOrientation.basePoint dual) (PolarOrientation.baseLine dual) hP hL
      (PolarOrientation.Inc dual) (PolarOrientation.incident_base dual)
      (fun g p l=>by rw [←hpoint,←hline];exact PolarOrientation.incident_smul dual (j g) p l)
      hflag (ep.symm p) (el.symm l)
    simpa only [ep,el,Equiv.apply_symm_apply] using hh
  · intro a p
    change (cp (ep.symm (j (f a) • p))).val=(a:G) • (cp (ep.symm p)).val
    rw [hpoint,hpact]
    exact S.pointedCosetEquiv_smul 0 1 _ a (ep.symm p)
  · intro a l
    change (cl (el.symm (j (f a) • l))).val=(a:G) • (cl (el.symm l)).val
    rw [hline,hlact]
    exact S.pointedCosetEquiv_smul 0 2 _ a (el.symm l)

/-- The original point quotient gives one of the two orientations, with its
literal quotient map and both original residue actions. -/
theorem exists_baseMark : ∃ dual : Bool, Nonempty (BaseMark S dual) := by
  rcases S.point_standard_quotientMark with ⟨e,h⟩ | ⟨e,h⟩
  · let f := S.localQuotientMap 0 e
    have hkP : f.ker≤localParabolic S.family 0 1 := by
      intro a ha
      exact S.T_le 1 (S.localQuotientMap_ker_le 0 e ha)
    have hkL : f.ker≤localParabolic S.family 0 2 := by
      intro a ha
      exact S.T_le 2 (S.localQuotientMap_ker_le 0 e ha)
    rcases h with ⟨hP,hL⟩ | ⟨hP,hL⟩
    · refine ⟨false,baseMark_of_quotient S false f (S.localQuotientMap_surjective 0 e)
        (S.localQuotientMap_ker 0 e) hkP hkL A6.subtype A6.subtype_injective
        (Or.inl (range_subtype A6)) (fun _ _=>rfl) (fun _ _=>rfl) ?_ ?_ ?_⟩
      · exact hP.trans a6_polarPoint_stabilizer_base.symm
      · exact hL.trans a6_polarLine_stabilizer_base.symm
      · exact PolarOrientation.a6_flag_transitive false
    · refine ⟨true,baseMark_of_quotient S true f (S.localQuotientMap_surjective 0 e)
        (S.localQuotientMap_ker 0 e) hkP hkL A6.subtype A6.subtype_injective
        (Or.inl (range_subtype A6)) (fun _ _=>rfl) (fun _ _=>rfl) ?_ ?_ ?_⟩
      · exact hP.trans a6_polarLine_stabilizer_base.symm
      · exact hL.trans a6_polarPoint_stabilizer_base.symm
      · exact PolarOrientation.a6_flag_transitive true
  · let f := S.localQuotientMap 0 e
    have hkP : f.ker≤localParabolic S.family 0 1 := by
      intro a ha
      exact S.T_le 1 (S.localQuotientMap_ker_le 0 e ha)
    have hkL : f.ker≤localParabolic S.family 0 2 := by
      intro a ha
      exact S.T_le 2 (S.localQuotientMap_ker_le 0 e ha)
    rcases h with ⟨hP,hL⟩ | ⟨hP,hL⟩
    · refine ⟨false,baseMark_of_quotient S false f (S.localQuotientMap_surjective 0 e)
        (S.localQuotientMap_ker 0 e) hkP hkL (MonoidHom.id S6) Function.injective_id
        (Or.inr (MonoidHom.range_eq_top.mpr Function.surjective_id))
        (fun _ _=>rfl) (fun _ _=>rfl) ?_ ?_ ?_⟩
      · exact hP.trans polarPoint_stabilizer_base.symm
      · exact hL.trans polarLine_stabilizer_base.symm
      · exact PolarOrientation.flag_transitive false
    · refine ⟨true,baseMark_of_quotient S true f (S.localQuotientMap_surjective 0 e)
        (S.localQuotientMap_ker 0 e) hkP hkL (MonoidHom.id S6) Function.injective_id
        (Or.inr (MonoidHom.range_eq_top.mpr Function.surjective_id))
        (fun _ _=>rfl) (fun _ _=>rfl) ?_ ?_ ?_⟩
      · exact hP.trans polarLine_stabilizer_base.symm
      · exact hL.trans polarPoint_stabilizer_base.symm
      · exact PolarOrientation.flag_transitive true
end PolarPointResidues
end Quasithin.I5.DSystem
