module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeEven.ReflectionAction
public import Theory.SpecificGroups.PSL3.SmallCompletion.LineGeneration

/-!
# Recognition by the literal point actions

The affine calculation determines the native right action. Its Borel and one
reflection generate the native line parabolic; the whole middle supplies all
remaining extension factors. Thus the point comparison intertwines both full
endpoints. Their paired completion then has injective projections, since each
point action is faithful. No plane coordinatization or ambient order bound is
assumed.

Source: Aschbacher–Smith F.4.8–9, printed pp.278–279. This proves a marked
comparison for these linear-three inputs as a consequence of their actions;
the source application requires only faithful extension recognition.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3.SmallCompletion
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven.Completion
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {E : SourceExtension F} {G : Type*} [Group G]
variable (c : Completion E G)
variable (ho : c.left.range⊓c.right.range=c.middle.range) {n : ℕ} (hF : Nat.card F=2^n)
variable (dc : ∀v w,c.graph.dist v w≤3) (hq : 2 < Nat.card F)
include ho hF dc hq

/-- The native right action is determined by its Borel and reflection. -/
theorem nativeCoordinates_right (a : lineParabolic F) (x : Point c.family) :
    c.nativeCoordinates ho hF dc (c.right (E.nativeRight a) • x)=
      a.val • c.nativeCoordinates ho hF dc x := by
  let e := c.nativeCoordinates ho hF dc
  let f : lineParabolic F →* Equiv.Perm (AffinePoints.Points F) :=
    e.permCongrHom.toMonoidHom.comp ((MulAction.toPermHom G (Point c.family)).comp
      (c.right.comp E.nativeRight))
  let g : lineParabolic F →* Equiv.Perm (AffinePoints.Points F) :=
    (MulAction.toPermHom PSL(3,F) (AffinePoints.Points F)).comp (lineParabolic F).subtype
  let K := f.eqLocus g
  have hm (a : lineParabolic F) : a∈K ↔ ∀x,e (c.right (E.nativeRight a) • x)=a.val • e x := by
    constructor
    · intro ha x
      have hh := Equiv.congr_fun (show f a=g a from ha) (e x)
      change e (c.right (E.nativeRight a) • e.symm (e x))=a.val • e x at hh
      rwa [e.symm_apply_apply] at hh
    · intro ha
      apply Equiv.ext
      intro y
      change e (c.right (E.nativeRight a) • e.symm y)=a.val • y
      exact (ha (e.symm y)).trans (congrArg (a.val • ·) (e.apply_symm_apply y))
  have hb : borel F ≤ K.map (lineParabolic F).subtype := by
    intro b hb
    refine ⟨nativeBorelRight ⟨b,hb⟩,(hm _).mpr ?_,rfl⟩
    intro y
    rw [←c.nativeBorel_right]
    exact c.nativeCoordinates_borel ho hF dc ⟨b,hb⟩ y
  have hw : reflection F true ∈ K.map (lineParabolic F).subtype := by
    refine ⟨⟨reflection F true,by exact reflection_mem F true⟩,(hm _).mpr ?_,rfl⟩
    exact c.nativeCoordinates_lineReflection ho hF dc hq
  obtain ⟨b,hb,he⟩ := AffinePoints.line_le_of_borel_reflection F _ hb hw a.property
  have he' : b=a := Subtype.ext he
  subst b
  exact (hm a).mp hb x

/-- The point comparison also preserves the native right endpoint. -/
theorem pointComparison_native_right (a : lineParabolic F) (x : Point c.family) :
    c.pointComparison E.model ho (E.completion_overlap _) hF dc (E.model_diameter hF)
      (c.right (E.nativeRight a) • x) =
    E.model.right (E.nativeRight a) •
      c.pointComparison E.model ho (E.completion_overlap _) hF dc (E.model_diameter hF) x := by
  have hh := congrArg E.modelPointEquiv (c.nativeCoordinates_right ho hF dc hq a x)
  rw [E.modelPointEquiv_smul] at hh
  simpa only [nativeCoordinates,Equiv.trans_apply,Equiv.apply_symm_apply,E.model_right_native] using hh

/-- All outer factors are carried by the whole middle, so the full right
endpoint acts through the same point comparison. -/
theorem pointComparison_right (a : E.right) (x : Point c.family) :
    c.pointComparison E.model ho (E.completion_overlap _) hF dc (E.model_diameter hF)
      (c.right a • x) =
    E.model.right a •
      c.pointComparison E.model ho (E.completion_overlap _) hF dc (E.model_diameter hF) x := by
  obtain ⟨b,hb,d,hd,he⟩ := E.right_factor (native_conj_injective F) a a.property
  let d' : E.middle := ⟨d,hd⟩
  have ha : a=E.nativeRight ⟨b,hb⟩*E.amalgam.right d' := Subtype.ext he
  have hc := DFunLike.congr_fun c.compatible d'
  have hm := DFunLike.congr_fun E.model.compatible d'
  change c.left (E.amalgam.left d')=c.right (E.amalgam.right d') at hc
  change E.model.left (E.amalgam.left d')=E.model.right (E.amalgam.right d') at hm
  rw [ha,map_mul,map_mul,mul_smul,mul_smul,←hc,c.pointComparison_native_right ho hF dc hq,
    c.pointComparison_left,hm]

/-- Both literal projections of the paired completion intertwine on all points. -/
theorem pair_point_action (z : c.Pair E.model) (x : Point c.family) :
    c.pointComparison E.model ho (E.completion_overlap _) hF dc (E.model_diameter hF)
      (c.pairFst E.model z • x) =
    c.pairSnd E.model z •
      c.pointComparison E.model ho (E.completion_overlap _) hF dc (E.model_diameter hF) x := by
  let e := c.pointComparison E.model ho (E.completion_overlap _) hF dc (E.model_diameter hF)
  let f := e.permCongrHom.toMonoidHom.comp
    ((MulAction.toPermHom G (Point c.family)).comp (c.pairFst E.model))
  let g := (MulAction.toPermHom E.carrier (Point (family E.model))).comp (c.pairSnd E.model)
  have hm (a : c.Pair E.model) : a∈f.eqLocus g ↔
      ∀x,e (c.pairFst E.model a • x)=c.pairSnd E.model a • e x := by
    constructor
    · intro ha x
      have hh := Equiv.congr_fun (show f a=g a from ha) (e x)
      change e (c.pairFst E.model a • e.symm (e x))=c.pairSnd E.model a • e x at hh
      rwa [e.symm_apply_apply] at hh
    · intro ha
      apply Equiv.ext
      intro y
      change e (c.pairFst E.model a • e.symm y)=c.pairSnd E.model a • y
      exact (ha (e.symm y)).trans (congrArg (c.pairSnd E.model a • ·) (e.apply_symm_apply y))
  have ht : (⊤ : Subgroup (c.Pair E.model)) ≤ f.eqLocus g := by
    rw [←(c.pairCompletion E.model).generated]
    apply sup_le
    · rintro _ ⟨a,rfl⟩
      apply (hm _).mpr
      intro y
      rw [c.pairFst_left,c.pairSnd_left]
      exact c.pointComparison_left _ _ _ _ _ _ a y
    · rintro _ ⟨a,rfl⟩
      apply (hm _).mpr
      intro y
      rw [c.pairFst_right,c.pairSnd_right]
      exact c.pointComparison_right ho hF dc hq a y
  exact (hm z).mp (ht (mem_top z)) x

variable [Finite G]
/-- The paired projections are bijective because their point actions are faithful. -/
theorem exists_extension_equiv : ∃ f : G ≃* E.carrier,
    (∀a : E.left,f (c.left a)=E.model.left a) ∧
    (∀a : E.right,f (c.right a)=E.model.right a) := by
  let e := c.pointComparison E.model ho (E.completion_overlap _) hF dc (E.model_diameter hF)
  have hi : Function.Injective (c.pairFst E.model) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro z hz
    have hz' : c.pairFst E.model z=1 := hz
    have hs : c.pairSnd E.model z=1 := by
      apply point_action_injective E.model (E.completion_overlap _) hF (E.model_diameter hF)
      apply Equiv.ext
      intro y
      obtain ⟨x,rfl⟩ := e.surjective y
      have hh := c.pair_point_action ho hF dc hq z x
      rw [hz',one_smul] at hh
      change c.pairSnd E.model z • e x=(1 : E.carrier) • e x
      rw [one_smul]
      exact hh.symm
    exact Subtype.ext (Prod.ext hz' hs)
  have hj : Function.Injective (c.pairSnd E.model) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro z hz
    have hz' : c.pairSnd E.model z=1 := hz
    have hf : c.pairFst E.model z=1 := by
      apply c.point_action_injective ho hF dc
      apply Equiv.ext
      intro x
      change c.pairFst E.model z • x=(1 : G) • x
      rw [one_smul]
      apply e.injective
      have hh := c.pair_point_action ho hF dc hq z x
      rw [hz',one_smul] at hh
      exact hh
    exact Subtype.ext (Prod.ext hf hz')
  let f : c.Pair E.model ≃* G := MulEquiv.ofBijective (c.pairFst E.model)
    ⟨hi,(c.firstCover E.model ho).surjective⟩
  let g : c.Pair E.model ≃* E.carrier := MulEquiv.ofBijective (c.pairSnd E.model)
    ⟨hj,(c.secondCover E.model ho (E.completion_overlap _)).surjective⟩
  refine ⟨f.symm.trans g,?_,?_⟩
  · intro a
    have ha : f.symm (c.left a)=(c.pairCompletion E.model).left a := by
      apply f.injective
      exact (f.apply_symm_apply _).trans (c.pairFst_left E.model a).symm
    change g (f.symm (c.left a))=_
    rw [ha]
    exact c.pairSnd_left E.model a
  · intro a
    have ha : f.symm (c.right a)=(c.pairCompletion E.model).right a := by
      apply f.injective
      exact (f.apply_symm_apply _).trans (c.pairFst_right E.model a).symm
    change g (f.symm (c.right a))=_
    rw [ha]
    exact c.pairSnd_right E.model a
end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven.Completion
