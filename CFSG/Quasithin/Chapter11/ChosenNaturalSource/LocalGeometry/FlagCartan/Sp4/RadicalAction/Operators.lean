module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.RadicalAction.Setup

/-!
# The natural plane kernel of the original local join

The original LT operators normalize the full natural symplectic image.
Restriction to the aligned field plane gives an irreducible binary action
of L₂T: its L₂ subgroup surjects onto the natural SL₂ action. The kernel
intersects L₂ in its two-core and has a two-group quotient, so it is exactly
O₂(L₂T). This also embeds the original plane-local core in R₂.

Source: Aschbacher--Smith, 11.2.4, printed pp.769--770.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix
open scoped MatrixGroups IsMulCommutative
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.RadicalAction
open PlaneAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

theorem field_card_gt_two : 2 < Nat.card S.field.Carrier := by
  rw [S.field.card_eq]
  simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) S.nonbinary

theorem ambientOperator_mem_normalizer (g : ambientJoin D) :
    linearAction (ambientAction S m) g ∈ naturalNormalizer := by
  let N := L.subgroupOf (ambientJoin D)
  have himage : N.map (linearAction (ambientAction S m)) = naturalDerivedImage := by
    apply le_antisymm
    · rintro _ ⟨l,hl,rfl⟩
      have he : linearAction (ambientAction S m) l =
          SymplecticNaturalNormalizer.naturalHom ((Coordinates.sp4 m).quotientMap ⟨l,hl⟩) :=
        LinearEquiv.ext (ambientAction_component S m ⟨l,hl⟩)
      rw [he]
      exact SymplecticNaturalNormalizer.naturalHom_mem (field_card_gt_two S) _
    · rintro _ ⟨a,rfl⟩
      obtain ⟨l,hl⟩ := (Coordinates.sp4 m).quotientMap_surjective a.val
      refine ⟨inclusion le_sup_left l,l.property,?_⟩
      apply LinearEquiv.ext
      intro w
      rw [linearAction_apply,ambientAction_component,hl]
      rfl
  change linearAction (ambientAction S m) g ∈ normalizer (naturalDerivedImage (F := S.field.Carrier) : Set _)
  rw [←himage]
  apply N.le_normalizer_map
  apply mem_map_of_mem
  have : N.Normal := normal_subgroupOf_of_le_normalizer (ambientJoin_normalizes_component (D := D))
  rw [normalizer_eq_top]
  trivial

def localJoin : Subgroup G := (flag m S).Li 1 ⊔ (T : Subgroup G)

theorem localJoin_le_ambient : localJoin S m ≤ ambientJoin D :=
  sup_le (((localResidual_le _).trans inf_le_left).trans le_sup_left) le_sup_right

theorem localJoin_normalizes_plane : localJoin S m ≤ normalizer ((flag m S).Vi 1 : Set G) :=
  sup_le ((localResidual_le _).trans inf_le_right) ((flag m S).invariant 1)

def quotientPlaneAction : Representation (ZMod 2) (localJoin S m) ((flag m S).space 1) :=
  Subrepresentation.toRepresentation
    (ρ := (ambientAction S m).comp (inclusion (localJoin_le_ambient S m)))
    { toSubmodule := ((flag m S).space 1).restrictScalars (ZMod 2)
      apply_mem_toSubmodule := by
        intro g v hv
        obtain ⟨w,hw⟩ := (Coordinates.sp4 m).projection_surjective (Multiplicative.ofAdd v)
        have hw' : ((Coordinates.sp4 m).projection w).toAdd = v := congrArg Multiplicative.toAdd hw
        have hwP : (w : G) ∈ (flag m S).Vi 1 :=
          ((Coordinates.sp4 m).mem_preimage _ w).mpr (hw'.symm ▸ hv)
        change ambientAction S m (inclusion (localJoin_le_ambient S m) g) v ∈ _
        rw [←hw']
        change (Coordinates.sp4 m).conjugationAction _ _ _ _ ∈ _
        rw [Coordinates.conjugationAction_projection]
        apply ((Coordinates.sp4 m).mem_preimage _ _).mp
        exact ((localJoin_normalizes_plane S m g.property) w.val).mp hwP }


theorem quotientPlaneAction_component (l : (flag m S).Li 1) (v : (flag m S).space 1) :
    quotientPlaneAction S m (inclusion le_sup_left l) v = planeAction S m l v := by
  apply Subtype.ext
  exact ambientAction_component S m ⟨l,(localResidual_le _ l.property).1⟩ v.val

theorem quotientPlaneAction_irreducible : (quotientPlaneAction S m).IsIrreducible := by
  let e := alignedPlaneCoordinates S m
  let : Nontrivial ((flag m S).space 1) := e.toEquiv.nontrivial
  refine ⟨?_⟩
  intro W
  by_cases hz : W = ⊥
  · exact Or.inl hz
  right
  have hz' : W.toSubmodule ≠ ⊥ := fun h => hz (Subrepresentation.toSubmodule_injective h)
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hz'
  apply top_unique
  intro w _
  by_cases hw : w = 0
  · exact hw ▸ W.toSubmodule.zero_mem
  obtain ⟨a,ha⟩ := Matrix.SL2.exists_mulVec_eq S.field.Carrier (e v) (e w)
    (fun h => hv0 (e.injective (h.trans e.map_zero.symm)))
    (fun h => hw (e.injective (h.trans e.map_zero.symm)))
  obtain ⟨l,hl⟩ := planeProjection_surjective S m a
  have he : quotientPlaneAction S m (inclusion le_sup_left l) v = w := by
    rw [quotientPlaneAction_component]
    apply e.injective
    rw [alignedPlaneCoordinates_intertwines,hl]
    exact ha
  exact he ▸ W.apply_mem_toSubmodule (inclusion le_sup_left l) hv

theorem quotientPlaneAction_kernel_isTwoGroup : IsPGroup 2 (quotientPlaneAction S m).ker := by
  let J := localJoin S m
  let N := ((flag m S).Li 1).subgroupOf J
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le ((flag m S).Li 1).le_normalizer ((flag m S).sylow_normalizes_Li 1))
  have hgen : N ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup (show (flag m S).Li 1 ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hquot : IsPGroup 2 (J ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N ((T : Subgroup G).subgroupOf J)
      T.isPGroup'.comap_subtype hgen
  let ρ := quotientPlaneAction S m
  let q := (QuotientGroup.mk' N).comp ρ.ker.subtype
  have hqker : IsPGroup 2 q.ker := by
    let r : q.ker →* (flag m S).Li 1 :=
      (J.subtype.comp (ρ.ker.subtype.comp q.ker.subtype)).codRestrict _ (by
        intro x
        change x.val.val ∈ N
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hr : ∀ x : q.ker, r x ∈ pCore 2 ((flag m S).Li 1) := by
      intro x
      apply (planeAction_fixes_iff S m _).mp
      intro v
      rw [←quotientPlaneAction_component]
      exact LinearMap.congr_fun x.val.property v
    let r' : q.ker →* pCore 2 ((flag m S).Li 1) := r.codRestrict _ hr
    apply pCore_isPGroup.of_injective r'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 ((flag m S).Li 1) => (x.val : G)) hab
  have ht := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
  rw [comap_top] at ht
  exact ht.of_equiv topEquiv

theorem quotientPlaneAction_ker :
    (quotientPlaneAction S m).ker = pCore 2 (localJoin S m) := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance,quotientPlaneAction_kernel_isTwoGroup S m⟩
  · let := quotientPlaneAction_irreducible S m
    let : Finite ((flag m S).space 1) := Finite.of_injective
      (alignedPlaneCoordinates S m) (alignedPlaneCoordinates S m).injective
    exact normal_p_subgroup_le_ker _ _ pCore_isPGroup

theorem planeCore_le_radical : ((flag m S).Li 1).pCoreIn 2 ≤ (flag m S).Ri 1 := by
  rintro x ⟨l,hl,rfl⟩
  have ha : inclusion (show (flag m S).Li 1 ≤ localJoin S m from le_sup_left) l ∈
      (quotientPlaneAction S m).ker := by
    apply LinearMap.ext
    intro v
    exact (quotientPlaneAction_component S m l v).trans
      ((planeAction_fixes_iff S m l).mpr hl v)
  rw [quotientPlaneAction_ker] at ha
  exact mem_map_of_mem _ ha

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.RadicalAction
