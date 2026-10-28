module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.PlaneAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.PlaneAction
public import Theory.GroupTheory.PCoreQuotientJoinAction

/-!
# The Sylow plane centralizer lies in the literal radical

The existing natural-plane markings identify the kernel of L₂ on V₂ as
O₂(L₂). The kernel on L₂T is then an extension of two-groups: its intersection
with L₂ lies in O₂(L₂), and its quotient embeds in L₂T/L₂. Normality places
this full kernel in O₂(L₂T), giving the required Sylow centralizer bound.
Both natural rows use their original quotient maps; no splitting is used.

Source: Aschbacher--Smith, 11.1.1, 11.1.3 and 11.2.4, printed pp.761,765,769.
-/

public noncomputable section
set_option linter.style.haveILetI false
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Outside
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

theorem sylow_centralizer_le_radical_of_plane_kernel {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hkernel : f.Li 1 ⊓ centralizer (f.Vi 1:Set G)≤(f.Li 1).pCoreIn 2) :
    (T:Subgroup G) ⊓ centralizer (f.Vi 1:Set G)≤f.Ri 1 := by
  let J := f.Li 1
  let W := f.Vi 1
  let M := J ⊔ (T:Subgroup G)
  let N := J.subgroupOf M
  have hMW : M≤normalizer (W:Set G) := sup_le
    ((localResidual_le _).trans inf_le_right) (f.invariant 1)
  let φ := W.normalizerMonoidHom.comp (inclusion hMW)
  letI : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le J.le_normalizer (f.sylow_normalizes_Li 1))
  have hgen : N ⊔ (T:Subgroup G).subgroupOf M=⊤ := by
    apply map_injective M.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le le_sup_right,
      ←MonoidHom.range_eq_map,range_subtype]
  have hquot : IsPGroup 2 (M ⧸ N) := isPGroup_quotient_of_sup_eq_top N
    ((T:Subgroup G).subgroupOf M) T.isPGroup'.comap_subtype hgen
  let q := (QuotientGroup.mk' N).comp φ.ker.subtype
  have hq : IsPGroup 2 q.ker := by
    let r : q.ker →* J :=
      (M.subtype.comp (φ.ker.subtype.comp q.ker.subtype)).codRestrict J (by
        intro x
        change x.val.val∈N
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hr : ∀x:q.ker,r x∈pCore 2 J := by
      intro x
      have hC : ((r x):G)∈centralizer (W:Set G) := by
        apply mem_centralizer_iff.mpr
        intro w hw
        have hh := congrArg (fun a : MulAut W => (a ⟨w,hw⟩:G)) x.val.property
        change ((r x):G)*w*((r x):G)⁻¹=w at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm
      have hh := hkernel ⟨(r x).property,hC⟩
      change r x∈((pCore 2 J).map J.subtype).comap J.subtype at hh
      rwa [comap_map_eq_self_of_injective J.subtype_injective] at hh
    let r' : q.ker →* pCore 2 J := r.codRestrict _ hr
    apply pCore_isPGroup.of_injective r'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x:pCore 2 J => (x.val:G)) hab
  have hker : IsPGroup 2 φ.ker := by
    have hh := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hq
    rw [comap_top] at hh
    exact hh.of_equiv topEquiv
  have hk : φ.ker≤pCore 2 M := le_sSup ⟨inferInstance,hker⟩
  intro t ht
  let t' : M := ⟨t,(le_sup_right : (T:Subgroup G)≤M) ht.1⟩
  have htker : t'∈φ.ker := by
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp ht.2 v.val v.property).symm
  exact mem_map_of_mem M.subtype (hk htker)

theorem plane_kernel_of_natural_action {c : Coordinates D S.field} (f : InvariantFlag c)
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : π.ker=pCore 2 (f.Li 1))
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ (a:f.Li 1) v,
      p (Components.flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v)=
        specialLinearNatural 2 (π a) (p v)) :
    f.Li 1 ⊓ centralizer (f.Vi 1:Set G)≤(f.Li 1).pCoreIn 2 := by
  intro a ha
  let a' : f.Li 1 := ⟨a,ha.1⟩
  have hlin (x:Fin 2 → S.field.Carrier) : specialLinearNatural 2 (π a') x=x := by
    obtain ⟨v,rfl⟩ := hp x
    rw [←hact]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp ha.2 v.toMul v.toMul.property).symm
  have hid : π a'=1 := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    have hh := congrFun (hlin (Pi.single j 1)) i
    change ((π a').val.mulVec (Pi.single j 1)) i=((Pi.single j 1 : Fin 2 → S.field.Carrier)) i at hh
    change (π a').val i j=(1 : Matrix (Fin 2) (Fin 2) S.field.Carrier) i j
    simpa [Matrix.mulVec_single, Pi.single_apply, Matrix.one_apply] using hh
  exact mem_map_of_mem (f.Li 1).subtype (hπ ▸ (show a'∈π.ker from hid))

theorem plane_kernel {c : Coordinates D S.field} (f : InvariantFlag c)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))) :
    f.Li 1 ⊓ centralizer (f.Vi 1:Set G)≤(f.Li 1).pCoreIn 2 := by
  cases c with
  | g2 m => exact (hG2 ⟨m⟩).elim
  | sl3 m =>
    have he : f=SL3.flag D S m := by
      have hspace : f.space=(SL3.flag D S m).space := by
        funext i
        exact SL3.flag_unique D S m i (f.space i) (f.dimension i) (f.invariant i)
      exact (show ∀ (a b : InvariantFlag (Coordinates.sl3 m)), a.space=b.space → a=b from
        fun ⟨_,_,_,_⟩ ⟨_,_,_,_⟩ h => by cases h; rfl) f (SL3.flag D S m) hspace
    subst f
    exact plane_kernel_of_natural_action (SL3.flag D S m)
      (SL3.PlaneAction.planeProjection D S m) (SL3.PlaneAction.planeProjection_ker D S m)
      (SL3.PlaneAction.planeEquiv D S m).toLinearMap
      (SL3.PlaneAction.planeEquiv D S m).surjective
      (SL3.PlaneAction.planeEquiv_intertwines D S m)
  | sp4 m =>
    have he : f=Sp4.flag m S := by
      have hspace : f.space=(Sp4.flag m S).space := by
        funext i
        exact Sp4.flag_unique m S i (f.space i) (f.dimension i) (f.invariant i)
      exact (show ∀ (a b : InvariantFlag (Coordinates.sp4 m)), a.space=b.space → a=b from
        fun ⟨_,_,_,_⟩ ⟨_,_,_,_⟩ h => by cases h; rfl) f (Sp4.flag m S) hspace
    subst f
    exact plane_kernel_of_natural_action (Sp4.flag m S)
      (Sp4.PlaneAction.planeProjection S m) (Sp4.PlaneAction.planeProjection_ker S m)
      (Sp4.PlaneAction.planeMap S m) (Sp4.PlaneAction.planeMap_surjective S m)
      (Sp4.PlaneAction.planeMap_intertwines S m)

theorem sylow_plane_centralizer_le_radical {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))) :
    (T:Subgroup G) ⊓ centralizer (f.Vi 1:Set G)≤f.Ri 1 :=
  sylow_centralizer_le_radical_of_plane_kernel f (plane_kernel f hG2)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Outside
