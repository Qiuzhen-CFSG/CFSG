module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationPrefix
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Completion
public import Theory.GroupTheory.ReducedNormal.Equiv

/-!
# Constructing the original F.7.6 geometry for LT and H

An escaping overgroup H of T supplies the second vertex group. Uniqueness
of N_G(L) forces the two-core of J=⟨LT,H⟩ to vanish: its nontriviality would
put N_G(O₂(J)), and hence H, inside N_G(L). Characteristic two of LT,
reducedness of the original V and C_T(V)=O₂(LT) supply the other F.7.6
hypotheses. The entire geometry is built inside J; explicit image lemmas
identify its seed and common Sylow with the original V and T.

No global normality or equality J=G is assumed. The Structural1222 input
is the permitted earlier source implication. Selection of H is separate.
Source: Aschbacher–Smith, 12.4.1, printed p.812, using 1.1.4, 1.2.7,
3.2.2(8), 12.2.2 and F.7.6.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Section02 ChapterF.Section07
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

abbrev localFamily (T : Sylow 2 G) (L H : Subgroup G) :=
  Geometry.family (L ⊔ (T : Subgroup G)) H

/-- Normalizer uniqueness removes the two-core of the actual generated group.
The normality used here is relative to that generated group. -/
theorem generated_core_eq_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hHM : ¬ H ≤ normalizer (L : Set G)) :
    pCore 2 (L ⊔ (T : Subgroup G) ⊔ H : Subgroup G) = ⊥ := by
  let J := L ⊔ (T : Subgroup G) ⊔ H
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right.trans le_sup_left
  have hQT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTJ] using
      pCoreIn_le_sylow J (T.subtype hTJ)
  have hJN : J ≤ normalizer (J.pCoreIn 2 : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hQ : J.pCoreIn 2 = ⊥ := by
    by_contra hn
    exact hHM ((le_sup_right.trans hJN).trans
      (D.normal_subgroup_normalizer_le h.toHypothesis1221
        (hQT.trans le_sup_right) hn (le_sup_left.trans hJN)))
  exact (map_eq_bot_iff_of_injective _ J.subtype_injective).mp hQ

private def firstEquiv (T : Sylow 2 G) (L H : Subgroup G) :
    (L ⊔ (T : Subgroup G) : Subgroup G) ≃* localFamily T L H false :=
  (subgroupOfEquivOfLe (show L ⊔ (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) ⊔ H
    from le_sup_left)).symm

omit [Finite G] in
private theorem firstEquiv_seed (T : Sylow 2 G) (L V H : Subgroup G) :
    (V.subgroupOf (L ⊔ (T : Subgroup G))).map (firstEquiv T L H).toMonoidHom =
      (V.subgroupOf (L ⊔ (T : Subgroup G) ⊔ H)).subgroupOf (localFamily T L H false) := by
  ext x
  rw [mem_map_equiv]
  rfl

/-- The actual F.7.6 setup for LT and an escaping local overgroup of T.
All action-kernel, reducedness and core-freeness conditions are proved. -/
noncomputable def localGeometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
  have hred := ((structural G T L h).2.2 V D).2.1
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
    rw [← RecognitionSource.chosen_sylow_centralizer_eq_core h D structural]
    apply le_antisymm
    · rintro x ⟨ht, y, hy, rfl⟩
      exact ⟨ht, fun v hv => congrArg Subtype.val (hy ⟨v, D.le_sylow.trans le_sup_right hv⟩ hv)⟩
    · rintro x ⟨ht, hc⟩
      exact ⟨ht, ⟨x, mem_sup_right ht⟩,
        fun v hv => Subtype.ext (hc v hv), rfl⟩

variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
  (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
  (hTH : (T : Subgroup G) ≤ H) (hHM : ¬ H ≤ normalizer (L : Set G))

/-- The geometric seed maps to the original chosen subgroup, exactly. -/
theorem localGeometry_seed_map :
    (localGeometry h D structural hTH hHM).seed.map
      (L ⊔ (T : Subgroup G) ⊔ H).subtype = V := by
  change (((V.subgroupOf (L ⊔ (T : Subgroup G) ⊔ H)).subgroupOf
    (localFamily T L H false)).map (localFamily T L H false).subtype).map _ = V
  rw [map_subgroupOf_eq_of_le
    (show V.subgroupOf (L ⊔ (T : Subgroup G) ⊔ H) ≤ localFamily T L H false
      from comap_mono (D.le_sylow.trans le_sup_right)),
    map_subgroupOf_eq_of_le (D.le_sylow.trans (le_sup_right.trans le_sup_left))]

/-- The common Sylow of the two vertex groups maps to the original T. -/
theorem localGeometry_sylow_map :
    (((localGeometry h D structural hTH hHM).sylow false :
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
theorem localGeometry_ne_bot : (localGeometry h D structural hTH hHM).V ≠ ⊥ := by
  intro he
  have hs : (localGeometry h D structural hTH hHM).seed = ⊥ := by
    rw [Track.SourceSetup.seed, he, Subgroup.map_bot]
  apply D.ne_bot
  rw [← localGeometry_seed_map h D structural hTH hHM, hs, Subgroup.map_bot]

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
