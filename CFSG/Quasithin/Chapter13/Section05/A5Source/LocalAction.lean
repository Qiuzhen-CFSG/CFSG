module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalStructure
public import Theory.SpecificGroups.SymmetricFive.RadicalRange
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PGroup.CharacteristicKernel

/-!
# Reducedness and the Sylow kernel of the original A₅ module

The original normalizer action restricts to LT with image containing A₅.
Every such subgroup of S₅ has trivial solvable radical, so the actual
centralizer quotient has trivial two-core. This proves reducedness of V.
When T normalizes L, the action kernel is a two-group: its intersection
with L is O₂(L), and its image in LT/L is a two-group. Its kernel is
therefore O₂(LT), giving the source Sylow-centralizer identity.

Source: Aschbacher–Smith 13.2.3(1) and the standing F.9.1 setup used
in 13.5.7, printed pp.878 and917.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

noncomputable def localActor : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 5) :=
  d.flag.normalizerAction.comp (inclusion (sup_le d.chosen.normalizes d.flag.T_normalizes))

theorem alternating_le_localActor : alternatingGroup (Fin 5) ≤ d.localActor.range := by
  intro a ha
  obtain ⟨l,hl⟩ := d.flag.module.onto ⟨a,ha⟩
  refine ⟨inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) l, ?_⟩
  change d.flag.normalizerAction ⟨l,_⟩ = a
  exact (d.flag.action_agrees l (d.flag.module.normalizes l.property)).trans
    (congrArg Subtype.val hl)

theorem localActor_kernel : d.localActor.ker =
    centralizer (V.subgroupOf (L ⊔ (T : Subgroup G)) : Set (L ⊔ (T : Subgroup G) : Subgroup G)) := by
  ext l
  rw [MonoidHom.mem_ker]
  change d.flag.normalizerAction ⟨l,_⟩ = 1 ↔ _
  rw [actor_eq_one_iff]
  constructor
  · intro hc v hv
    exact Subtype.ext (hc v.val hv)
  · intro hc v hv
    exact congrArg Subtype.val (hc ⟨v,(le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G))
      (d.chosen.le_sylow hv)⟩ hv)

theorem localActor_core : pCore 2 d.localActor.range = ⊥ := by
  let : Group.IsNilpotent (pCore 2 d.localActor.range) := pCore_isPGroup.isNilpotent
  have h := le_solvableRadical (pCore 2 d.localActor.range) inferInstance inferInstance
  rw [Theory.SpecificGroups.FivePointSylowParabolic.radical_eq_bot_of_alternating_le
    d.localActor.range d.alternating_le_localActor] at h
  exact bot_unique h

/-- The original chosen module is reduced, by its actual five-point action. -/
theorem reduced : IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) := by
  let := d.elementary
  have hV : V ≤ L ⊔ (T : Subgroup G) := d.chosen.le_sylow.trans le_sup_right
  let hN : (V.subgroupOf (L ⊔ (T : Subgroup G))).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le d.chosen.normalizes d.flag.T_normalizes)
  refine ⟨hN,IsElementaryAbelian.subgroupOf hV,?_⟩
  let e := QuotientGroup.liftEquiv
    (centralizer (V.subgroupOf (L ⊔ (T : Subgroup G)) : Set (L ⊔ (T : Subgroup G) : Subgroup G)))
    d.localActor.rangeRestrict_surjective
    (d.localActor.ker_rangeRestrict.trans d.localActor_kernel).symm
  have h := pCore_map_iso 2 e
  rw [d.localActor_core] at h
  exact (map_eq_bot_iff_of_injective _ e.injective).mp h

/-- The literal local kernel is a two-group when T normalizes L. -/
theorem localActor_kernel_isTwo
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    IsPGroup 2 d.localActor.ker := by
  let J := L ⊔ (T : Subgroup G)
  let B := L.subgroupOf J
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTL)
  have hgen : (T : Subgroup G).subgroupOf J ⊔ B = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_right,map_subgroupOf_eq_of_le le_sup_left,
      ← MonoidHom.range_eq_map,range_subtype,sup_comm]
  have hquot : IsPGroup 2 (J ⧸ B) := quotient_isPGroup_of_sup_eq_top
    ((T : Subgroup G).subgroupOf J) B T.isPGroup'.comap_subtype hgen
  let r : d.localActor.ker →* J ⧸ B :=
    (QuotientGroup.mk' B).comp d.localActor.ker.subtype
  have hr : IsPGroup 2 r.ker := by
    let i : r.ker →* pCore 2 L :=
      { toFun := fun x => by
          have hx : (x.val.val.val : G) ∈ L := (QuotientGroup.eq_one_iff (N := B) x.val.val).mp x.property
          refine ⟨⟨x.val.val.val,hx⟩,?_⟩
          have ha : d.flag.module.action ⟨x.val.val.val,hx⟩ = 1 := by
            apply Subtype.ext
            have hh : d.localActor x.val.val = 1 := x.val.property
            change d.flag.normalizerAction ⟨x.val.val.val,_⟩ = 1 at hh
            exact (d.flag.action_agrees ⟨x.val.val.val,hx⟩
              (d.flag.module.normalizes hx)).symm.trans hh
          exact d.flag.action_kernel ▸ ha
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact pCore_isPGroup.of_injective i (fun x y he => Subtype.ext (Subtype.ext
      (Subtype.ext (congrArg (fun z : pCore 2 L => ((z : L) : G)) he))))
  have hh := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup r hr
  rw [comap_top] at hh
  exact hh.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup d.localActor.ker) ≃* d.localActor.ker)

/-- The original action has precisely the local two-core as kernel. -/
theorem localActor_kernel_eq_core
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    d.localActor.ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  have hk : IsPGroup 2 d.localActor.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact d.localActor_kernel_isTwo hTL
  have h := d.localActor.rangeRestrict.comap_pCore_of_ker_isPGroup
    d.localActor.rangeRestrict_surjective hk
  rw [d.localActor_core,MonoidHom.comap_bot,MonoidHom.ker_rangeRestrict] at h
  exact h

/-- The standing source Sylow-centralizer identity, derived internally. -/
theorem sylow_centralizer
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) = (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  apply le_antisymm
  · intro x hx
    let x' : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨x,(le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)) hx.1⟩
    have hk : x' ∈ d.localActor.ker :=
      (actor_eq_one_iff d.flag ⟨x,d.flag.T_normalizes hx.1⟩).mpr hx.2
    exact mem_map_of_mem (L ⊔ (T : Subgroup G)).subtype
        (show x' ∈ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) from
          d.localActor_kernel_eq_core hTL ▸ hk)
  · apply le_inf
    · simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
        pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    · exact d.chosen.core_centralizes

/-- Original 13.2.3(1), on both literal local centralizers. -/
theorem local_centralizers
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
        (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      (L ⊔ (T : Subgroup G)) ⊓ centralizer (V₃ : Set G) =
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hfirst : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    apply le_antisymm
    · intro x hx
      let x' : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨x,hx.1⟩
      have hk : x' ∈ d.localActor.ker := (actor_eq_one_iff d.flag
        ⟨x,(sup_le d.chosen.normalizes d.flag.T_normalizes) hx.1⟩).mpr hx.2
      exact mem_map_of_mem (L ⊔ (T : Subgroup G)).subtype
        (show x' ∈ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) from
          d.localActor_kernel_eq_core hTL ▸ hk)
    · exact le_inf (pCoreIn_le 2 _) d.chosen.core_centralizes
  refine ⟨hfirst,?_⟩
  rw [← hfirst]
  apply le_antisymm
  · intro x hx
    exact ⟨hx.1,(centralizer_third d.flag V₃ d.third_le d.third_card d.third_invariant).le
      ⟨(sup_le d.chosen.normalizes d.flag.T_normalizes) hx.1,hx.2⟩⟩
  · exact inf_le_inf_left _ (centralizer_le d.third_le)

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
