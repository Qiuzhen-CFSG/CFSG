module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Setup
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Reduced
/-!
# The actual doubled critical-pair setup

Put W=V_M and Q=C_T(W). The proved full-orbit reducedness and Frattini
argument retain the whole action in A=N_M(Q). Its two-core is Q, and
condition E makes A characteristic two. Since LT lies in A, the original
maximal-overgroup uniqueness gives O₂(⟨A,H⟩)=1 for every outside H.
These facts construct all of F.7.6 on the literal A, H and W. The seed and
Sylow transport theorems identify the graph data with the original groups.

Source: Aschbacher--Smith, 11.3.6, printed p.772, using 11.0.3(1),
F.7.6 and the Frattini argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- The exact N_M(Q_M) used in the doubled critical-pair argument. -/
@[expose] def criticalLocal (T : Sylow 2 G) (L V : Subgroup G) : Subgroup G :=
  normalizer (L : Set G) ⊓
    normalizer (((T : Subgroup G) ⊓ centralizer (fullModule L V : Set G)) : Set G)

include D S in
/-- The original LT normalizes C_T(V_M), so it lies in the critical local. -/
theorem local_join_le_criticalLocal :
    L ⊔ (T : Subgroup G) ≤ criticalLocal T L V :=
  le_inf (sup_le L.le_normalizer D.sylow_normalizes_component)
    (local_join_normalizes_fullModule_centralizer (D := D) (S := S))

/-- The full module lies in the first vertex group. -/
theorem fullModule_le_criticalLocal (d : Coordinates D S) :
    fullModule L V ≤ criticalLocal T L V :=
  (fullModule_le_sylow d).trans
    (le_sup_right.trans (local_join_le_criticalLocal (D := D) (S := S)))

/-- Frattini preserves full-orbit reducedness and identifies its Sylow centralizer. -/
theorem criticalLocal_reduced (d : Coordinates D S) :
    IsPReduced 2 ((fullModule L V).subgroupOf (criticalLocal T L V)) ∧
    (T : Subgroup G).subgroupOf (criticalLocal T L V) ⊓
      centralizer ((fullModule L V).subgroupOf (criticalLocal T L V) :
        Set (criticalLocal T L V)) = pCore 2 (criticalLocal T L V) := by
  have hr : IsPReduced 2 ((fullModule L V).subgroupOf (normalizer (L : Set G))) :=
    LocalGeometry.Preliminary.fullModule_reduced D S
  exact (reduced_normalizer_local (normalizer (L : Set G)) (fullModule L V) T
    ((fullModule_le_sylow d).trans D.sylow_normalizes_component)
    D.sylow_normalizes_component hr).2.2

omit [Finite G] in
/-- The first vertex group preserves the full original module. -/
theorem criticalLocal_normalizes :
    criticalLocal T L V ≤ normalizer (fullModule L V : Set G) :=
  inf_le_left.trans normalizes_fullModule

/-- Condition E applies to the actual Sylow-containing two-local. -/
theorem criticalLocal_characteristic (d : Coordinates D S) :
    generalizedFitting (criticalLocal T L V) = pCore 2 (criticalLocal T L V) := by
  have hQ : (T : Subgroup G) ⊓ centralizer (fullModule L V : Set G) ≠ ⊥ := by
    let := fullModule_elementary d
    exact fun hz => fullModule_ne_bot (D := D)
      (le_bot_iff.mp ((le_inf (fullModule_le_sylow d) (fullModule L V).le_centralizer).trans hz.le))
  have hn := (doubled_hypothesisE61 d).normalizer_sylowCentralizer_le
  have he : criticalLocal T L V =
      normalizer (((T : Subgroup G) ⊓ centralizer (fullModule L V : Set G)) : Set G) :=
    inf_eq_right.mpr hn
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply Chapter1.mem_He_iff.mp
  apply Chapter1.twoLocal_mem_He_of_sylow_le T (S.source.simpleQTKE.evenCharacteristic T)
  · exact ⟨_,hQ,T.isPGroup'.to_le inf_le_left,he⟩
  · exact le_sup_right.trans (local_join_le_criticalLocal (D := D) (S := S))

include D S in
/-- Uniqueness over LT makes the generated amalgam group core-free. -/
theorem criticalLocal_generated_core {H : Subgroup G}
    (hout : ¬ H ≤ normalizer (L : Set G)) :
    pCore 2 (criticalLocal T L V ⊔ H : Subgroup G) = ⊥ := by
  apply twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup _ H
    (normalizer (L : Set G)) _ hout
  intro K hK hAK
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    S.source.simpleQTKE T S.source.maximal_faithful.1
  have hh := hu.normalizer_unique K hK
  have he : componentOrbit L (T : Subgroup G) = L := D.localOrbit_eq
  rw [he] at hh
  exact hh ((local_join_le_criticalLocal (D := D) (S := S)).trans hAK)
open CFSG.Quasithin.ChapterF.Section07
/-- The literal doubled critical-pair family inside ⟨N_M(Q_M),H⟩. -/
abbrev criticalFamily (H : Subgroup G) := ChapterF.Section07.Geometry.family (criticalLocal T L V) H

/-- Construct every F.7.6 premise on N_M(Q_M), H and the full original V_M. -/
def criticalSetup (d : Coordinates D S) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hout : ¬ H ≤ normalizer (L : Set G)) : Track.SourceSetup (criticalFamily (T := T) (L := L) (V := V) H) := by
  let A := criticalLocal T L V
  let J := A ⊔ H
  let F := criticalFamily (T := T) (L := L) (V := V) H
  let P := T.subtype (show (T : Subgroup G) ≤ J from (le_sup_right.trans (local_join_le_criticalLocal (D := D) (S := S))).trans le_sup_left)
  have hPi (i : Bool) : (P : Subgroup J) ≤ F i := by
    cases i
    · exact fun _ hx => le_sup_right.trans (local_join_le_criticalLocal (D := D) (S := S)) hx
    · exact fun _ hx => hTH hx
  let Q (i : Bool) := P.subtype (hPi i)
  let E : A ≃* F false :=
    (subgroupOfEquivOfLe (show A ≤ J from le_sup_left)).symm
  have hm : ((fullModule L V).subgroupOf A).map E.toMonoidHom = ((fullModule L V).subgroupOf J).subgroupOf (F false) := by
    ext x
    rw [mem_map_equiv]
    rfl
  have hr := (criticalLocal_reduced d).1.map_equiv E
  rw [hm] at hr
  refine {
    finite := fun _ => inferInstance
    generates := ChapterF.Section07.Geometry.family_generates A H
    characteristicTwo := ?_
    core_free := ?_
    sylow := Q
    same_sylow := ?_
    V := ((fullModule L V).subgroupOf J).subgroupOf (F false)
    reduced := hr
    centralizer_eq := ?_ }
  · rw [← map_generalizedFitting_equiv E, criticalLocal_characteristic d, pCore_map_iso]
  · let e : (F false ⊔ F true : Subgroup J) ≃* J :=
      (MulEquiv.subgroupCongr (ChapterF.Section07.Geometry.family_generates A H)).trans Subgroup.topEquiv
    apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
    rw [pCore_map_iso]
    exact criticalLocal_generated_core (D := D) (S := S) hout
  · exact (map_subgroupOf_eq_of_le (hPi false)).trans (map_subgroupOf_eq_of_le (hPi true)).symm
  · rw [AmalgamLocalCores.reduced_centralizer_core _ hr]
    apply map_injective (f := E.symm.toMonoidHom) E.symm.injective
    rw [Subgroup.map_inf _ _ _ E.symm.injective, pCore_map_iso]
    have hQ : (Q false : Subgroup (F false)).map E.symm.toMonoidHom =
        (T : Subgroup G).subgroupOf A := by
      ext x
      rw [mem_map_equiv]
      rfl
    rw [hQ, map_centralizer_equiv]
    have hVV : E.symm '' (((fullModule L V).subgroupOf J).subgroupOf (F false) : Set (F false)) =
        ((fullModule L V).subgroupOf A : Set A) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨E x, hx, E.symm_apply_apply x⟩
    rw [hVV]
    exact (criticalLocal_reduced d).2

variable (d : Coordinates D S) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hout : ¬ H ≤ normalizer (L : Set G))

/-- The graph seed embeds back to the full original V_M. -/
theorem criticalSeed_map :
    (criticalSetup d H hTH hout).seed.map (criticalLocal T L V ⊔ H).subtype = fullModule L V := by
  change ((((fullModule L V).subgroupOf (criticalLocal T L V ⊔ H)).subgroupOf
    (criticalFamily (T := T) (L := L) (V := V) H false)).map
      (criticalFamily (T := T) (L := L) (V := V) H false).subtype).map _ = fullModule L V
  have hV : (fullModule L V).subgroupOf (criticalLocal T L V ⊔ H) ≤
      criticalFamily (T := T) (L := L) (V := V) H false := fun _ hx => fullModule_le_criticalLocal d hx
  rw [map_subgroupOf_eq_of_le hV,
    map_subgroupOf_eq_of_le ((fullModule_le_criticalLocal d).trans le_sup_left)]

/-- The original nonzero seed lies in V_M, so the doubled track seed is nonzero. -/
theorem criticalSeed_ne_bot : (criticalSetup d H hTH hout).V ≠ ⊥ := by
  intro he
  have hs : (criticalSetup d H hTH hout).seed = ⊥ := by
    rw [Track.SourceSetup.seed, he, Subgroup.map_bot]
  apply fullModule_ne_bot (D := D)
  rw [← criticalSeed_map d H hTH hout, hs, Subgroup.map_bot]

/-- The common Sylow in the graph embeds back to the original T. -/
theorem criticalSylow_map :
    (((criticalSetup d H hTH hout).sylow false :
      Subgroup (criticalFamily (T := T) (L := L) (V := V) H false)).map
      (criticalFamily (T := T) (L := L) (V := V) H false).subtype).map
        (criticalLocal T L V ⊔ H).subtype = (T : Subgroup G) := by
  change (((T : Subgroup G).subgroupOf (criticalLocal T L V ⊔ H)).subgroupOf
    (criticalFamily (T := T) (L := L) (V := V) H false) |>.map
      (criticalFamily (T := T) (L := L) (V := V) H false).subtype).map _ = _
  have hT : (T : Subgroup G).subgroupOf (criticalLocal T L V ⊔ H) ≤
      criticalFamily (T := T) (L := L) (V := V) H false := fun _ hx => le_sup_right.trans (local_join_le_criticalLocal (D := D) (S := S)) hx
  rw [map_subgroupOf_eq_of_le hT,
    map_subgroupOf_eq_of_le ((le_sup_right.trans (local_join_le_criticalLocal (D := D) (S := S))).trans le_sup_left)]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
