module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.GeometryReductions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Theory.Representation.FirstCohomologyAutomorphism.FixedSupplement
public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeLargeField
public import Theory.GroupTheory.PCoreRestriction

/-!
# Sylow placement after the common-core construction

The natural SL₃ cohomology theorem splits O₂(LT) as V C_T(L).
The fixed-space conclusion of 11.3.7 eliminates C_T(L), using the
intersection with Ω₁Z(T). Once the odd-degree argument supplies T = T_L,
this proves containment in the original L and its actual Sylow placement.
The equality T = T_L remains an explicit source obligation.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
printed p.774; C.1.13(b), with its corrected factor V C_T(L).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

include D

theorem sylow_centralizer_of_omega_fixed
    (hz : omegaCenter T ⊓ centralizer (L : Set G) = ⊥) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  apply subgroup_eq_bot_of_central_omega_disjoint (T := T) _ inf_le_left
  · exact (le_inf (T : Subgroup G).le_normalizer
      (D.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  · apply bot_unique
    exact (le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans hz.le

omit [Finite G] in
theorem sylow_centralizer_le_join_core :
    (T : Subgroup G) ⊓ centralizer (L : Set G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
    (inf_le_left.trans le_sup_right)
  apply sup_le
  · exact (le_centralizer_iff.mp (show (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
      centralizer (L : Set G) from inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  · exact (le_inf (T : Subgroup G).le_normalizer
      (D.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf

omit [Finite G] in
theorem join_core_commutator (hcore : L.pCoreIn 2 = V) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, L⁆ ≤ V := by
  have hn : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ normalizer (L : Set G) :=
    (pCoreIn_le _ _).trans (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hLQ : L ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    (le_sup_left : L ≤ L ⊔ (T : Subgroup G)).trans
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  exact (le_inf (le_normalizer_iff_commutator_le_right.mp hn)
    (le_normalizer_iff_commutator_le_left.mp hLQ)).trans
      ((inf_pCoreIn_le_of_le 2 le_sup_left).trans hcore.le)

variable (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
include S m

theorem join_core_supplement (hcore : L.pCoreIn 2 = V)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      V ⊔ ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (L : Set G)) := by
  let c := Coordinates.sl3 m
  have hi : Function.Injective c.projection := by
    apply c.projection.ker_eq_bot_iff.mp
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact mem_bot.mp (hfixed ▸ (show (v : G) ∈ V ⊓ centralizer (L : Set G) from
      ⟨v.property, (c.projection_eq_one_iff v).mp hv⟩))
  let e : V ≃* Multiplicative (Fin 3 → S.field.Carrier) :=
    MulEquiv.ofBijective c.projection ⟨hi,c.projection_surjective⟩
  let q : L →* Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier :=
    m.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q :=
    m.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have hF : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) S.nonbinary
  let : Subsingleton (OneCohomology.H1 (specialLinearNatural (k := S.field.Carrier) 3)) :=
    OneCohomology.SLHigherNatural.H1_subsingleton_sl3_large_field hF
  apply OneCohomology.eq_sup_inf_centralizer_of_H1_zero
    (k := S.field.Carrier) (A := Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier) L V _
    (hcore ▸ pCoreIn_le 2 L) D.le_core q hq
    e (specialLinearNatural (k := S.field.Carrier) 3)
  · intro l w
    have he := c.projection_component_conjugation l (e.symm (Multiplicative.ofAdd w))
    have hw : (e (e.symm (Multiplicative.ofAdd w))).toAdd = w := by
      rw [e.apply_symm_apply]
      rfl
    change (e (V.normalizerMonoidHom (inclusion D.normalizes l)
      (e.symm (Multiplicative.ofAdd w)))).toAdd =
        specialLinearNatural (k := S.field.Carrier) 3 (q l)
          (e (e.symm (Multiplicative.ofAdd w))).toAdd at he
    rw [hw] at he
    have he' := congrArg e.symm (congrArg Multiplicative.ofAdd he)
    rw [ofAdd_toAdd, e.symm_apply_apply] at he'
    exact (congrArg Subtype.val he').symm
  · have hk : q.ker = pCore 2 L := by
      ext l
      change m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 ↔ _
      rw [m.groupEquiv.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff l
    rw [hk]
    change L.pCoreIn 2 ≤ _
    rw [hcore]
    exact le_centralizer_iff.mp D.core_centralizes
  · exact join_core_commutator D hcore

theorem join_core_eq_seed_sup_sylow_centralizer (hcore : L.pCoreIn 2 = V)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ T := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hc : (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (L : Set G) =
      (T : Subgroup G) ⊓ centralizer (L : Set G) :=
    le_antisymm (inf_le_inf_right _ hQT)
      (le_inf (sylow_centralizer_le_join_core D) inf_le_right)
  rw [join_core_supplement D S m hcore hfixed, hc]

theorem join_core_eq (hcore : L.pCoreIn 2 = V)
    (hz : omegaCenter T ⊓ centralizer (L : Set G) = ⊥) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 = V := by
  rw [join_core_eq_seed_sup_sylow_centralizer D S m hcore
      (seed_fixed_eq_bot_of_omega_fixed D S hz),
    sylow_centralizer_of_omega_fixed D hz, sup_bot_eq]

theorem sylow_le_component (hcore : L.pCoreIn 2 = V)
    (hz : omegaCenter T ⊓ centralizer (L : Set G) = ⊥)
    (hT : sourceTL T L = (T : Subgroup G)) : (T : Subgroup G) ≤ L := by
  rw [← hT, sourceTL, join_core_eq D S m hcore hz,
    sup_eq_left.mpr (hcore ▸ pCoreIn_le 2 L)]
  exact inf_le_right

theorem sylow_placement (hcore : L.pCoreIn 2 = V)
    (hz : omegaCenter T ⊓ centralizer (L : Set G) = ⊥)
    (hT : sourceTL T L = (T : Subgroup G)) :
    ∃ t : Sylow 2 L, (t : Subgroup L).map L.subtype = (T : Subgroup G) := by
  have hTL := sylow_le_component D S m hcore hz hT
  exact ⟨T.subtype hTL, map_subgroupOf_eq_of_le hTL⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
