module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.PlaneAction
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.GroupTheory.PCoreQuotientJoinAction

/-!
# The full chosen symplectic action and its quotient kernel

The original LT action descends to the supplied natural coordinates. Its
kernel intersects L in O₂(L), and the remaining quotient is a two-group.
Thus this kernel lies in O₂(LT), which fixes the original chosen module.
Equality of quotient operators consequently gives equality on the entire
central cover, without a splitting or a vanishing-centralizer assumption.

Source: Aschbacher--Smith, 11.2.4, printed pp.769--770; the chosen module
lies in the reduced normal module of LT. The radical action consumes this
comparison to lift its natural matrix operators to the original V.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix
open scoped MatrixGroups IsMulCommutative
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair.Ambient
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.RadicalAction
open PlaneAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

def ambientJoin (_D : ChosenModule T L V) : Subgroup G := L ⊔ (T : Subgroup G)

omit [Finite G] in
theorem ambientJoin_normalizes_component : ambientJoin D ≤ normalizer (L : Set G) :=
  sup_le L.le_normalizer D.sylow_normalizes_component

include S in
theorem ambientJoin_normalizes_seed : ambientJoin D ≤ normalizer (V : Set G) :=
  sup_le D.normalizes S.sylow_normalizes

def ambientAction : Representation (ZMod 2) (ambientJoin D) (Vector S.field.Carrier) :=
  (Coordinates.sp4 m).conjugationAction
    (ambientJoin_normalizes_component (D := D)) (ambientJoin_normalizes_seed S)

theorem ambientAction_component (l : L) (w : Vector S.field.Carrier) :
    ambientAction S m (inclusion le_sup_left l) w =
      symplecticNatural 2 ((Coordinates.sp4 m).quotientMap l) w := by
  obtain ⟨v,hv⟩ := (Coordinates.sp4 m).projection_surjective (Multiplicative.ofAdd w)
  have he : ((Coordinates.sp4 m).projection v).toAdd = w := congrArg Multiplicative.toAdd hv
  rw [←he]
  change (Coordinates.sp4 m).conjugationAction _ _ _ _ = _
  rw [Coordinates.conjugationAction_projection]
  exact (Coordinates.sp4 m).projection_component_conjugation l v

theorem ambientAction_kernel_isTwoGroup : IsPGroup 2 (ambientAction S m).ker := by
  let J := ambientJoin D
  let N := L.subgroupOf J
  let : N.Normal := normal_subgroupOf_of_le_normalizer (ambientJoin_normalizes_component (D := D))
  have hgen : N ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup (show L ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hquot : IsPGroup 2 (J ⧸ N) := isPGroup_quotient_of_sup_eq_top N
    ((T : Subgroup G).subgroupOf J) T.isPGroup'.comap_subtype hgen
  let ρ := ambientAction S m
  let q := (QuotientGroup.mk' N).comp ρ.ker.subtype
  have hqker : IsPGroup 2 q.ker := by
    let r : q.ker →* L :=
      (J.subtype.comp (ρ.ker.subtype.comp q.ker.subtype)).codRestrict _ (by
        intro x
        change x.val.val ∈ N
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hr : ∀ x : q.ker, r x ∈ pCore 2 L := by
      intro x
      apply (QuotientGroup.eq_one_iff (N := pCore 2 L) (r x)).mp
      apply m.groupEquiv.injective
      rw [map_one]
      apply SymplecticNaturalNormalizer.naturalHom_injective
      apply LinearEquiv.ext
      intro w
      rw [map_one]
      change symplecticNatural 2 ((Coordinates.sp4 m).quotientMap (r x)) w = w
      rw [←ambientAction_component]
      exact LinearMap.congr_fun x.val.property w
    let r' : q.ker →* pCore 2 L := r.codRestrict _ hr
    apply pCore_isPGroup.of_injective r'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 L => (x.val : G)) hab
  have ht := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
  rw [comap_top] at ht
  exact ht.of_equiv topEquiv

theorem ambientAction_kernel_fixes (g : ambientJoin D) (hg : g ∈ (ambientAction S m).ker)
    (v : V) : V.normalizerMonoidHom (inclusion (ambientJoin_normalizes_seed S) g) v = v := by
  have hc : (ambientAction S m).ker ≤ pCore 2 (ambientJoin D) :=
    le_sSup ⟨inferInstance,ambientAction_kernel_isTwoGroup S m⟩
  apply Subtype.ext
  exact mul_inv_eq_iff_eq_mul.mpr
    (D.core_centralizes (mem_map_of_mem _ (hc hg)) v.val v.property).symm

theorem ambientAction_eq_iff (g h : ambientJoin D) :
    ambientAction S m g = ambientAction S m h ↔
      V.normalizerMonoidHom (inclusion (ambientJoin_normalizes_seed S) g) =
        V.normalizerMonoidHom (inclusion (ambientJoin_normalizes_seed S) h) := by
  constructor
  · intro he
    have hk : g*h⁻¹ ∈ (ambientAction S m).ker := by
      change ambientAction S m (g*h⁻¹) = 1
      rw [map_mul,he,←map_mul,mul_inv_cancel,map_one]
    have hf : V.normalizerMonoidHom
        (inclusion (ambientJoin_normalizes_seed S) (g*h⁻¹)) = 1 :=
      MulEquiv.ext (ambientAction_kernel_fixes S m _ hk)
    simpa only [map_mul,map_inv,mul_inv_eq_one] using hf
  · intro he
    apply LinearMap.ext
    intro w
    obtain ⟨v,hv⟩ := (Coordinates.sp4 m).projection_surjective (Multiplicative.ofAdd w)
    have hw : ((Coordinates.sp4 m).projection v).toAdd = w := congrArg Multiplicative.toAdd hv
    rw [←hw]
    change (Coordinates.sp4 m).conjugationAction _ _ _ _ =
      (Coordinates.sp4 m).conjugationAction _ _ _ _
    rw [Coordinates.conjugationAction_projection,Coordinates.conjugationAction_projection,he]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.RadicalAction
