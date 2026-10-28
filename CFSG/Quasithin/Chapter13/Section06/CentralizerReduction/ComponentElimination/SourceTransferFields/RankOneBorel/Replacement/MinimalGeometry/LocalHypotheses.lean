module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal

/-!
# Local hypotheses for the minimal rank-one replacement

SQTK is inherited from the involution centralizer. The earlier characteristic-two
identity for that centralizer restricts to K₀T_v because it contains the actual
Sylow T_v. These conclusions concern the intrinsic overgroup K₀T_v.

Its Sylow cannot be normal: intersect with the normal component, then map the
resulting Sylow onto the specified SL₂ model. A defining-characteristic Sylow
of SL₂ is not normal, as its normalizer is the proper upper triangular Borel.
Thus, once uniqueness of the maximal overgroup is proved, these deductions
supply the remaining B.6.1 and C.1.26 hypotheses. Uniqueness itself is still
an explicit premise of the consumer below.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.2–6 and 13.6.18, printed pp.926–931; Definition B.6.1, p.112.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry
open Subgroup Theory.GroupTheory ComponentSelection
open scoped MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- The full local-family minimality passes to the intrinsic overgroup with
its specified Sylow. No restriction to equal-image members is introduced. -/
theorem minimal_local_in_join (K₀ K T : Subgroup G) (v : G)
    (hmin : Minimal (fun D => D ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v)) K₀)
    (P : Sylow 2 (K₀ ⊔ Tv T v : Subgroup G))
    (hP : (P : Subgroup (K₀ ⊔ Tv T v : Subgroup G)).map
      (K₀ ⊔ Tv T v).subtype = Tv T v) :
    Minimal (fun D => D ∈ Chapter1.L (K₀ ⊔ Tv T v : Subgroup G) (P : Subgroup _))
      (K₀.subgroupOf (K₀ ⊔ Tv T v)) := by
  let H := K₀ ⊔ Tv T v
  have hPS : (Tv T v).subgroupOf H = (P : Subgroup H) := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (show Tv T v ≤ H from le_sup_right), hP]
  refine ⟨?_, ?_⟩
  · rw [← hPS]
    exact (Chapter1.mem_LIn_iff_subgroupOf
      (show Tv T v ≤ H from le_sup_right) (show K₀ ≤ H from le_sup_left)).mp
        ⟨le_sup_left, hmin.1.2⟩
  · intro D hD hDK
    have hDm : D.map H.subtype ∈ Chapter1.L G (Tv T v) := by
      have hm := (Chapter1.mem_L_map_iff H.subtype H.subtype_injective).mpr hD
      rwa [hP] at hm
    have hDmK : D.map H.subtype ≤ K₀ := by
      exact (map_mono (f := H.subtype) hDK).trans_eq
        (map_subgroupOf_eq_of_le (show K₀ ≤ H from le_sup_left))
    have hKD : K₀ ≤ D.map H.subtype :=
      hmin.2 ⟨hDmK.trans hmin.1.1, hDm⟩ hDmK
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    exact (map_subgroupOf_eq_of_le (show K₀ ≤ H from le_sup_left)).le.trans hKD

/-- The actual involution centralizer supplies the full local SQTK hypothesis. -/
theorem local_join_sqtk {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G) (K₀ T : Subgroup G) (v : G)
    (hv : orderOf v = 2) (hK₀ : K₀ ≤ Gv v) :
    IsSQTK 𝒦 (K₀ ⊔ Tv T v : Subgroup G) := by
  have hH : K₀ ⊔ Tv T v ≤ Gv v := sup_le hK₀ inf_le_right
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hH)).mp
    ((hG.involution_centralizer_sqtk hv).subgroup
      ((K₀ ⊔ Tv T v).subgroupOf (Gv v)))

/-- Source 13.6.6 and the actual Sylow embedding supply characteristic two locally. -/
theorem local_join_characteristic_two
    (K₀ T : Subgroup G) (v : G) (hK₀ : K₀ ≤ Gv v)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v)) :
    generalizedFitting (K₀ ⊔ Tv T v : Subgroup G) =
      pCore 2 (K₀ ⊔ Tv T v : Subgroup G) := by
  let H := K₀ ⊔ Tv T v
  have hH : H ≤ Gv v := sup_le hK₀ inf_le_right
  obtain ⟨S, hS⟩ := hSylow
  have hSH : (S : Subgroup (Gv v)).map (Gv v).subtype ≤ H := hS ▸ le_sup_right
  have hchar : HasCharacteristicTwo (Gv v) := by
    change centralizer (pCore 2 (Gv v) : Set (Gv v)) ≤ pCore 2 (Gv v)
    rw [← hf]
    exact centralizer_generalizedFitting_le (Gv v)
  have hc : HasCharacteristicTwo (H.subgroupOf (Gv v)) :=
    centralizer_pCore_le_of_sylow_le S (H.subgroupOf (Gv v))
      (map_le_iff_le_comap.mp hSH) hchar
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    (hc.of_equiv (subgroupOfEquivOfLe hH))
private theorem sl2_sylow_not_normal {F : Type*} [Field F] [Finite F] [CharP F 2]
    (S : Sylow 2 (SL(2, F))) : ¬ (S : Subgroup (SL(2, F))).Normal := by
  intro hn
  let := hn
  let U := Matrix.SpecialLinearGroup.upperUnipotentSylow F 2
  have he : (U : Subgroup (SL(2, F))) = S :=
    S.is_maximal' U.isPGroup' (S.isPGroup'.le_sylow_of_normal U)
  change Matrix.SpecialLinearGroup.upperUnipotent F = (S : Subgroup (SL(2, F))) at he
  have hnU : (Matrix.SpecialLinearGroup.upperUnipotent F).Normal := he.symm ▸ hn
  let := hnU
  have ht : Matrix.SpecialLinearGroup.rankOneBorel F = ⊤ := normalizer_eq_top _
  let w : SL(2, F) := Matrix.SpecialLinearGroup.transvection
    (i := (1 : Fin 2)) (j := 0) one_ne_zero 1
  have hw : w ∈ Matrix.SpecialLinearGroup.rankOneBorel F := ht ▸ mem_top w
  have he := (Matrix.SpecialLinearGroup.mem_rankOneBorel_iff w).mp hw
  simp [w, Matrix.SpecialLinearGroup.transvection_coe] at he

private theorem sylow_not_normal_of_rankOne_image
    {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
    (D : Subgroup H) [D.Normal] (f : D →* SL(2, F)) (hf : Function.Surjective f)
    (P : Sylow 2 H) : ¬ (P : Subgroup H).Normal := by
  intro hn
  let := hn
  obtain ⟨R, hR⟩ := P.exists_subgroupOf_eq_of_normal D
  have hnR : (R : Subgroup D).Normal := hR.symm ▸ inferInstance
  exact sl2_sylow_not_normal (R.mapSurjective hf) (hnR.map f hf)


/-- Every Sylow of K₀T_v is nonnormal when the actual component has a rank-one image. -/
theorem local_join_sylow_not_normal
    (K₀ L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K₀ : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : plusImage K₀ L T z v hL hz K₀ ≃* SL(2, F))
    (P : Sylow 2 (K₀ ⊔ Tv T v : Subgroup G)) :
    ¬ (P : Subgroup (K₀ ⊔ Tv T v : Subgroup G)).Normal := by
  let H := K₀ ⊔ Tv T v
  let D := K₀.subgroupOf H
  let : D.Normal := normal_subgroupOf_of_le_normalizer (sup_le K₀.le_normalizer hn)
  let i : D ≃* K₀ := subgroupOfEquivOfLe le_sup_left
  let f := e.toMonoidHom.comp ((componentMap K₀ L T z v hL hz).comp i.toMonoidHom)
  exact sylow_not_normal_of_rankOne_image D f
    (e.surjective.comp ((componentMap_surjective K₀ L T z v hL hz).comp i.surjective)) P
/-- The remaining B.6.1 premise is uniqueness; nonnormality is derived from
the actual model, for every Sylow with the specified ambient image. -/
theorem local_minimalParabolic_of_unique_maximal
    (K₀ L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K₀ : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : plusImage K₀ L T z v hL hz K₀ ≃* SL(2, F))
    (hmax : ∀ P : Sylow 2 (K₀ ⊔ Tv T v : Subgroup G),
      (P : Subgroup (K₀ ⊔ Tv T v : Subgroup G)).map (K₀ ⊔ Tv T v).subtype = Tv T v →
        ∃! M : Subgroup (K₀ ⊔ Tv T v : Subgroup G), IsCoatom M ∧ (P : Subgroup _) ≤ M) :
    ∀ P : Sylow 2 (K₀ ⊔ Tv T v : Subgroup G),
      (P : Subgroup (K₀ ⊔ Tv T v : Subgroup G)).map (K₀ ⊔ Tv T v).subtype = Tv T v →
        ChapterB.IsMinimalParabolicOver P ⊤ := by
  intro P hP
  exact (ChapterB.isMinimalParabolicOver_top_iff P).mpr
    ⟨hmax P hP, local_join_sylow_not_normal K₀ L T z v hL hz hn e P⟩

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
open HigherFieldParabolics

/-- Apply the existing C.1.26 consumer after proving unique maximality.
SQTK, characteristic two and nonnormality require no additional geometric
premises. The actual earlier 13.6.16(2) remains `hpush`; the independent
C.1.26 implication remains `source`. This is not the uniqueness theorem. -/
theorem block_alternatives_of_unique_maximal {𝒦 : GroupClass.{u}}
    (choices : DistinguishedPairs.{u}) (source : C126Source 𝒦 choices)
    (hG : IsSimpleQTKE 𝒦 G)
    (K₀ L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hv : orderOf v = 2)
    (hlocal : K₀ ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hn : Tv T v ≤ normalizer (K₀ : Set G))
    (hpush : CharacteristicNormalizerObstruction (Tv T v) K₀)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : plusImage K₀ L T z v hL hz K₀ ≃* SL(2, F))
    (hmax : ∀ P : Sylow 2 (K₀ ⊔ Tv T v : Subgroup G),
      (P : Subgroup (K₀ ⊔ Tv T v : Subgroup G)).map (K₀ ⊔ Tv T v).subtype = Tv T v →
        ∃! M : Subgroup (K₀ ⊔ Tv T v : Subgroup G), IsCoatom M ∧ (P : Subgroup _) ≤ M) :
    ChapterC.IsBlock (K₀.subgroupOf (K₀ ⊔ Tv T v)) ∧
      ((∃ n, ChapterC.IsL2EvenBlock K₀ n) ∨ ChapterC.IsAlternatingBlock K₀ 5) :=
  block_alternatives_of_C126 choices source (Tv T v) K₀ hlocal.2 hn hpush
    (local_join_sqtk hG K₀ T v hv hlocal.1)
    (local_join_characteristic_two K₀ T v hlocal.1 hSylow hf)
    (local_minimalParabolic_of_unique_maximal K₀ L T z v hL hz hn e hmax)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry

end
