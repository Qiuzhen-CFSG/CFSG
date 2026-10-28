module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalGeometry
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAt.Basic
import all CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalGeometry

/-!
# The literal F.7.6 geometry with the same-G,T structural input

The original proof only uses structural 12.2.2 at this ambient group and
Sylow subgroup. Retain its generated subgroup, two vertex groups, chosen
seed and subtype inclusions, while accepting exactly Structural1222At.
The internal import shares the original private vertex equivalence; all
existing universal interfaces remain unchanged.
Source: Aschbacher–Smith, 12.4.1, printed p.812, and F.7.6.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Section02 ChapterF.Section07
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The actual F.7.6 setup for LT and an escaping local overgroup of T.
All action-kernel, reducedness and core-freeness conditions are proved. -/
noncomputable def localGeometryAt
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hTH : (T : Subgroup G) ≤ H) (hHM : ¬ H ≤ normalizer (L : Set G)) :
    Track.SourceSetup (localFamily T L H) := by
  let J := L ⊔ (T : Subgroup G) ⊔ H
  let F := localFamily T L H
  let P₀ := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right.trans le_sup_left)
  have hPi (i : Bool) : (P₀ : Subgroup J) ≤ F i := by
    cases i
    · exact fun x hx => mem_sup_right hx
    · exact fun x hx => hTH hx
  let S (i : Bool) := P₀.subtype (hPi i)
  let E := firstEquiv T L H
  have hred := ((structural L h).2.2 V D).2.1
  have hV := hred.map_equiv E
  rw [firstEquiv_seed] at hV
  refine {
    finite := fun _ => inferInstance
    generates := Geometry.family_generates _ _
    characteristicTwo := ?_
    core_free := ?_
    sylow := S
    same_sylow := ?_
    V := (V.subgroupOf J).subgroupOf (F false)
    reduced := hV
    centralizer_eq := ?_ }
  · have hc : HasCharacteristicTwo (L ⊔ (T : Subgroup G) : Subgroup G) :=
      Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)
        ⟨h.maximal_faithful.1.1.2.2,
          fun x hx => (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)) hx⟩)
    rw [← map_generalizedFitting_equiv E,
      generalizedFitting_eq_pCore_of_selfCentralizing 2 hc, pCore_map_iso]
  · let e : (F false ⊔ F true : Subgroup J) ≃* J :=
      (MulEquiv.subgroupCongr (Geometry.family_generates _ _)).trans topEquiv
    apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
    rw [pCore_map_iso]
    exact generated_core_eq_bot h D hHM
  · exact (map_subgroupOf_eq_of_le (hPi false)).trans
      (map_subgroupOf_eq_of_le (hPi true)).symm
  · rw [AmalgamLocalCores.reduced_centralizer_core _ hV]
    apply map_injective (f := E.symm.toMonoidHom) E.symm.injective
    rw [Subgroup.map_inf _ _ _ E.symm.injective, pCore_map_iso]
    have hS : (S false : Subgroup (F false)).map E.symm.toMonoidHom =
        (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)) := by
      ext x
      rw [mem_map_equiv]
      rfl
    have hVV : E.symm '' ((V.subgroupOf J).subgroupOf (F false) : Set (F false)) =
        (V.subgroupOf (L ⊔ (T : Subgroup G)) : Set (L ⊔ (T : Subgroup G) : Subgroup G)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨E x, hx, E.symm_apply_apply x⟩
    rw [hS, map_centralizer_equiv, hVV]
    apply map_injective (f := (L ⊔ (T : Subgroup G)).subtype) Subtype.val_injective
    rw [Subgroup.map_inf _ _ _ Subtype.val_injective,
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)]
    change (T : Subgroup G) ⊓ _ = (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [← RecognitionSource.chosen_sylow_centralizer_eq_core_at h D structural]
    apply le_antisymm
    · rintro x ⟨ht, y, hy, rfl⟩
      exact ⟨ht, fun v hv => congrArg Subtype.val (hy ⟨v, D.le_sylow.trans le_sup_right hv⟩ hv)⟩
    · rintro x ⟨ht, hc⟩
      exact ⟨ht, ⟨x, mem_sup_right ht⟩,
        fun v hv => Subtype.ext (hc v hv), rfl⟩

variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
  (hTH : (T : Subgroup G) ≤ H) (hHM : ¬ H ≤ normalizer (L : Set G))

/-- The geometric seed maps to the original chosen subgroup, exactly. -/
theorem localGeometryAt_seed_map :
    (localGeometryAt h D structural hTH hHM).seed.map
      (L ⊔ (T : Subgroup G) ⊔ H).subtype = V := by
  change (((V.subgroupOf (L ⊔ (T : Subgroup G) ⊔ H)).subgroupOf
    (localFamily T L H false)).map (localFamily T L H false).subtype).map _ = V
  rw [map_subgroupOf_eq_of_le
    (show V.subgroupOf (L ⊔ (T : Subgroup G) ⊔ H) ≤ localFamily T L H false
      from comap_mono (D.le_sylow.trans le_sup_right)),
    map_subgroupOf_eq_of_le (D.le_sylow.trans (le_sup_right.trans le_sup_left))]

/-- The common Sylow of the two vertex groups maps to the original T. -/
theorem localGeometryAt_sylow_map :
    (((localGeometryAt h D structural hTH hHM).sylow false :
      Subgroup (localFamily T L H false)).map (localFamily T L H false).subtype).map
        (L ⊔ (T : Subgroup G) ⊔ H).subtype = (T : Subgroup G) := by
  change ((((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G) ⊔ H)).subgroupOf
    (localFamily T L H false)).map (localFamily T L H false).subtype).map _ = _
  rw [map_subgroupOf_eq_of_le
    (show (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G) ⊔ H) ≤
      localFamily T L H false from fun x hx => mem_sup_right hx),
    map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) ⊔ H
      from le_sup_right.trans le_sup_left)]

/-- The source choice, not an extra geometric assumption, makes the track defined. -/
theorem localGeometryAt_ne_bot : (localGeometryAt h D structural hTH hHM).V ≠ ⊥ := by
  intro he
  have hs : (localGeometryAt h D structural hTH hHM).seed = ⊥ := by
    rw [Track.SourceSetup.seed, he, Subgroup.map_bot]
  apply D.ne_bot
  rw [← localGeometryAt_seed_map h D structural hTH hHM, hs, Subgroup.map_bot]

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
