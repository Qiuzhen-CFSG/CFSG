module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.Chapter3.Section02.LocalCentralizer
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Completion
public import Theory.GroupTheory.ReducedNormal.Equiv
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# The original F.7.6 setup for a chosen natural module

Uniqueness over LT makes the two-core of <LT,H> trivial when H is outside
N_G(L). The original FSU seed is V because T normalizes V. Thus the earlier
reducedness and Sylow-centralizer theorems apply without changing that seed.
Transport to the actual generated group constructs every F.7.6 premise.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.2.5, printed p.770, using 3.2.2(8) and F.7.6, pp.579 and312.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterF.Section07
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

private theorem uniqueness :
    Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.source.simpleQTKE T S.source.maximal_faithful.1

/-- The preceding FSU reducedness applies to V itself, including its central part. -/
theorem seed_reduced : IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) := by
  have h := (D.fundamentalSetup S.source.toHypothesis1221).module_reduced (uniqueness D S)
  rw [S.unchanged_seed] at h
  change IsPReduced 2 (V.subgroupOf (Chapter3.Section02.localOrbit T L ⊔ (T : Subgroup G))) at h
  rwa [D.localOrbit_eq] at h

/-- Uniqueness for LT controls the full ambient normalizer of the original V. -/
theorem seed_normalizer_le : normalizer (V : Set G) ≤ normalizer (L : Set G) :=
  D.normal_subgroup_normalizer_le S.source.toHypothesis1221
    (D.le_sylow.trans le_sup_right) D.ne_bot (sup_le D.normalizes S.sylow_normalizes)

/-- The exact Sylow centralizer, with the unchanged original seed. -/
theorem seed_sylow_centralizer :
    (T : Subgroup G) ⊓ centralizer (V : Set G) = (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have h := (D.fundamentalSetup S.source.toHypothesis1221).sylow_centralizer_module
    (uniqueness D S)
  rw [S.unchanged_seed] at h
  simpa only [Chapter3.Section02.localJoin, D.localOrbit_eq] using h

/-- Leaving the original M=N_G(L) makes the actual generated two-core trivial. -/
theorem generated_core {H : Subgroup G} (hout : ¬ H ≤ normalizer (L : Set G)) :
    pCore 2 (L ⊔ (T : Subgroup G) ⊔ H : Subgroup G) = ⊥ := by
  apply twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup _ H
    (normalizer (L : Set G)) _ hout
  have hu := (uniqueness D S).normalizer_unique
  have he : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      D.sylow_normalizes_component) (le_componentOrbit L T)
  simpa only [he] using hu

/-- Condition E gives characteristic two for the literal LT. -/
private theorem characteristic_join :
    generalizedFitting (L ⊔ (T : Subgroup G) : Subgroup G) =
      pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
    (S.source.simpleQTKE.evenCharacteristic T)
    ⟨S.source.maximal_faithful.1.1.2.2, fun _ hx => mem_sup_right hx⟩)

/-- The Sylow centralizer equality inside LT, for transport into the graph. -/
private theorem intrinsic_centralizer :
    (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)) ⊓
      centralizer (V.subgroupOf (L ⊔ (T : Subgroup G)) : Set (L ⊔ (T : Subgroup G) : Subgroup G)) =
      pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  let A := L ⊔ (T : Subgroup G)
  apply map_injective A.subtype_injective
  rw [Subgroup.map_inf _ _ _ A.subtype_injective, map_subgroupOf_eq_of_le le_sup_right]
  change (T : Subgroup G) ⊓ _ = A.pCoreIn 2
  rw [← seed_sylow_centralizer D S]
  apply le_antisymm
  · rintro x ⟨ht, y, hy, rfl⟩
    exact ⟨ht, fun v hv => congrArg Subtype.val (hy ⟨v, D.le_sylow.trans le_sup_right hv⟩ hv)⟩
  · rintro x ⟨ht, hc⟩
    exact ⟨ht, ⟨x, mem_sup_right ht⟩, fun v hv => Subtype.ext (hc v hv), rfl⟩

/-- The literal family inside <LT,H>; its first vertex group is canonically LT. -/
abbrev family (H : Subgroup G) := Geometry.family (L ⊔ (T : Subgroup G)) H

private def firstEquiv (H : Subgroup G) :
    (L ⊔ (T : Subgroup G) : Subgroup G) ≃* (family (T := T) (L := L) H false) :=
  (subgroupOfEquivOfLe (show L ⊔ (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) ⊔ H from
    le_sup_left)).symm

/-- Construct F.7.6 on LT and the actual outside H. No critical pair is assumed. -/
def f7Setup (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hout : ¬ H ≤ normalizer (L : Set G)) : Track.SourceSetup (family (T := T) (L := L) H) := by
  let A := L ⊔ (T : Subgroup G)
  let J := A ⊔ H
  let F := family (T := T) (L := L) H
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right.trans le_sup_left)
  have hPi (i : Bool) : (P : Subgroup J) ≤ F i := by
    cases i
    · exact fun _ hx => mem_sup_right hx
    · exact fun _ hx => hTH hx
  let Q (i : Bool) := P.subtype (hPi i)
  let E := firstEquiv (T := T) (L := L) H
  have hm : (V.subgroupOf A).map E.toMonoidHom = (V.subgroupOf J).subgroupOf (F false) := by
    ext x
    rw [mem_map_equiv]
    rfl
  have hr := (seed_reduced D S).map_equiv E
  rw [hm] at hr
  refine {
    finite := fun _ => inferInstance
    generates := Geometry.family_generates A H
    characteristicTwo := ?_
    core_free := ?_
    sylow := Q
    same_sylow := ?_
    V := (V.subgroupOf J).subgroupOf (F false)
    reduced := hr
    centralizer_eq := ?_ }
  · rw [← map_generalizedFitting_equiv E, characteristic_join D S, pCore_map_iso]
  · let e : (F false ⊔ F true : Subgroup J) ≃* J :=
      (MulEquiv.subgroupCongr (Geometry.family_generates A H)).trans Subgroup.topEquiv
    apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
    rw [pCore_map_iso]
    exact generated_core D S hout
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
    have hVV : E.symm '' ((V.subgroupOf J).subgroupOf (F false) : Set (F false)) =
        (V.subgroupOf A : Set A) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨E x, hx, E.symm_apply_apply x⟩
    rw [hVV]
    exact intrinsic_centralizer D S

variable (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hout : ¬ H ≤ normalizer (L : Set G))

/-- The graph seed embeds back to precisely V. -/
theorem f7Seed_map :
    (f7Setup D S H hTH hout).seed.map (L ⊔ (T : Subgroup G) ⊔ H).subtype = V := by
  change (((V.subgroupOf (L ⊔ (T : Subgroup G) ⊔ H)).subgroupOf
    (family (T := T) (L := L) H false)).map
      (family (T := T) (L := L) H false).subtype).map _ = V
  have hV : V.subgroupOf (L ⊔ (T : Subgroup G) ⊔ H) ≤
      family (T := T) (L := L) H false := fun _ hx => D.le_sylow.trans le_sup_right hx
  rw [map_subgroupOf_eq_of_le hV,
    map_subgroupOf_eq_of_le (D.le_sylow.trans (le_sup_right.trans le_sup_left))]

/-- The original Irr+ choice supplies the nonzero seed required by the track. -/
theorem f7V_ne_bot : (f7Setup D S H hTH hout).V ≠ ⊥ := by
  intro he
  have hs : (f7Setup D S H hTH hout).seed = ⊥ := by
    rw [Track.SourceSetup.seed, he, Subgroup.map_bot]
  apply D.ne_bot
  rw [← f7Seed_map D S H hTH hout, hs, Subgroup.map_bot]

/-- The common Sylow in the graph embeds back to the original T. -/
theorem f7Sylow_map :
    (((f7Setup D S H hTH hout).sylow false :
      Subgroup (family (T := T) (L := L) H false)).map
      (family (T := T) (L := L) H false).subtype).map
        (L ⊔ (T : Subgroup G) ⊔ H).subtype = (T : Subgroup G) := by
  change (((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G) ⊔ H)).subgroupOf
    (family (T := T) (L := L) H false) |>.map
      (family (T := T) (L := L) H false).subtype).map _ = _
  have hT : (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G) ⊔ H) ≤
      family (T := T) (L := L) H false := fun _ hx => mem_sup_right hx
  rw [map_subgroupOf_eq_of_le hT,
    map_subgroupOf_eq_of_le (le_sup_right.trans le_sup_left)]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure
