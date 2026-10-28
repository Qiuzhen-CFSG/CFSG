module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.Actions
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups
public import Theory.GroupTheory.CubicSylowJoin
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Constructing the actual source minimal parabolic

The plus image of Lᵥ remains two-perfect. Its nontrivial action on z prevents
that image from being a two-group, while the earlier cubic two-core quotient
bounds its order by three times a power of two. Local-component membership
makes the image of Tᵥ ∩ K a Sylow two-subgroup of K⁺. Normalization therefore
gives index three for the literal image of Lᵥ(Tᵥ ∩ K).

The checked Bruhat and flag calculations in dimensions four and five now
construct a basis and omitted node, retaining the supplied SL model and the
actual Sylow image. Only the intrinsic geometric calculations housed under
Chapter 15 are reused; no later chapter source theorem is invoked. The final
consumer derives the middle-node conclusion once an outside actor is known.
The inner-action residual construction remains a separate obligation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the
minimal-parabolic argument in 13.6.22 and 13.6.23(2–3), printed pp.932–933,
PDF pp.949–950.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction
open ComponentSelection BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
namespace FlagRecognition
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification

private theorem four_coordinates (U : Sylow 2 (LinearGroup 4))
    (P : Subgroup (LinearGroup 4)) (hUP : (U : Subgroup (LinearGroup 4)) ≤ P) :
    ∃ (b : Basis 3) (cuts : Set (Fin 3)), P = cutStabilizer b cuts ∧
      (U : Subgroup (LinearGroup 4)) = cutStabilizer b Set.univ := by
  let : Finite (LinearGroup 4) :=
    Finite.of_injective (fun g : LinearGroup 4 => (g : Space 4 → Space 4)) DFunLike.coe_injective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (LinearGroup 4) Linear.Four.standardSylow U
  have hmap : Linear.Four.standardBorel.map (MulAut.conj g).toMonoidHom =
      (U : Subgroup (LinearGroup 4)) := by
    change ((g • Linear.Four.standardSylow : Sylow 2 (LinearGroup 4)) : Subgroup (LinearGroup 4)) = _
    rw [hg]
  let Q := P.map (MulAut.conj g).symm.toMonoidHom
  have hBQ : Linear.Four.standardBorel ≤ Q := by
    intro u hu
    apply Subgroup.mem_map_equiv.mpr
    apply hUP
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  obtain ⟨cuts, hQ⟩ := Linear.Four.standard_overgroups_of_bruhat
    Linear.Four.hasBruhatDecomposition Q hBQ
  have hQP : Q.map (MulAut.conj g).toMonoidHom = P :=
    (Subgroup.map_symm_eq_iff_map_eq Q (e := MulAut.conj g) (H := P)).mp rfl
  refine ⟨Linear.Four.standardBasis.map g, cuts, ?_, ?_⟩
  · rw [← hQP, hQ]
    exact cutStabilizer_map_conj _ _ _
  · rw [← hmap]
    exact cutStabilizer_map_conj _ _ _

private theorem five_coordinates (U : Sylow 2 (LinearGroup 5))
    (P : Subgroup (LinearGroup 5)) (hUP : (U : Subgroup (LinearGroup 5)) ≤ P) :
    ∃ (b : Basis 4) (cuts : Set (Fin 4)), P = cutStabilizer b cuts ∧
      (U : Subgroup (LinearGroup 5)) = cutStabilizer b Set.univ := by
  obtain ⟨b, hb⟩ := sylow_eq_cutStabilizer U
  obtain ⟨c, cuts, hc⟩ := BinaryLinear.FiveFlagGeometry.isFlagParabolic_of_sylow_le U P hUP
  change P = cutStabilizer c cuts at hc
  refine ⟨b, cuts, hc.trans (cutStabilizer_eq_of_fullFlag_le b c cuts ?_), hb⟩
  rw [← hc, ← hb]
  exact hUP

/-- The marked subgroup is reconstructed from its index, retaining a basis for its Sylow. -/
theorem exists_minimalParabolic {m : ℕ} (hm : m = 3 ∨ m = 4)
    (U : Sylow 2 (LinearGroup (m + 1)))
    (P : Subgroup (LinearGroup (m + 1))) (hUP : (U : Subgroup _) ≤ P)
    (hi : (U : Subgroup _).relIndex P = 3) :
    ∃ (b : Basis m) (i : Fin m), P = minimalParabolic b i ∧
      (U : Subgroup _) = cutStabilizer b Set.univ := by
  have hc : ∃ (b : Basis m) (cuts : Set (Fin m)), P = cutStabilizer b cuts ∧
      (U : Subgroup _) = cutStabilizer b Set.univ := by
    rcases hm with rfl | rfl
    · exact four_coordinates U P hUP
    · exact five_coordinates U P hUP
  obtain ⟨b, cuts, hP, hU⟩ := hc
  rw [hP, hU] at hi
  obtain ⟨i, rfl⟩ := Linear.cuts_eq_compl_singleton_of_index_three b cuts hi
  exact ⟨b, i, hP, hU⟩
end FlagRecognition

variable {G : Type*} [Group G]

/-- Restrict the literal plus map to any subgroup of its actor. -/
def plusImageMap (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (H : Subgroup G) (hH : H ≤ plusActor K L T v) :
    H →* plusImage K L T z v hL hz H :=
  ((plusMk K L T z v hL hz).subgroupMap (H.subgroupOf (plusActor K L T v))).comp
    (subgroupOfEquivOfLe hH).symm.toMonoidHom

theorem plusImageMap_surjective (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (H : Subgroup G) (hH : H ≤ plusActor K L T v) :
    Function.Surjective (plusImageMap K L T z v hL hz H hH) :=
  ((plusMk K L T z v hL hz).subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hH).symm.surjective

/-- Mapping the source product retains the intersection before quotienting. -/
theorem sourceParabolic_plusImage (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    plusImage K L T z v hL hz (sourceParabolic K L T v) =
      plusImage K L T z v hL hz (Lv L v) ⊔
        plusImage K L T z v hL hz (Tv T v ⊓ K) := by
  have hLa : Lv L v ≤ plusActor K L T v := le_sup_right.trans le_sup_left
  have hTa : Tv T v ⊓ K ≤ plusActor K L T v := inf_le_left.trans le_sup_right
  rw [plusImage, sourceParabolic, subgroupOf_sup hLa hTa, Subgroup.map_sup]
  rfl

/-- Local-family membership supplies the actual component Sylow intersection. -/
theorem plusSylowIntersection [Finite G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hlocal : K ∈ Chapter1.LIn (Gv v) (Tv T v)) :
    Chapter1.IsSylowIn 2 (plusImage K L T z v hL hz (Tv T v ⊓ K))
      (plusImage K L T z v hL hz K) := by
  have hs := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hlocal.2.2.1 le_sup_left hlocal.2.1.subnormal
  have hs' : Chapter1.IsSylowIn 2
      ((Tv T v ⊓ K).subgroupOf (plusActor K L T v))
      (K.subgroupOf (plusActor K L T v)) := by
    apply (Chapter1.IsSylowIn.map_iff _ (plusActor K L T v).subtype_injective).mp
    simpa only [map_subgroupOf_eq_of_le (K_le_plusActor K L T v),
      map_subgroupOf_eq_of_le (inf_le_right.trans (K_le_plusActor K L T v))] using hs
  exact Chapter1.Section02.IndexTwo.isSylowIn_map hs' (plusMk K L T z v hL hz)

/-- The earlier cubic two-core quotient bounds the order of the literal Lᵥ plus image. -/
theorem plusLv_card_dvd [Finite G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3) :
    ∃ n, Nat.card (plusImage K L T z v hL hz (Lv L v)) ∣ 3 * 2 ^ n := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Lv L v)).exists_card_eq
  have hsize : Nat.card (Lv L v) = 3 * 2 ^ n := by
    rw [← (pCore 2 (Lv L v)).index_mul_card, index_eq_card, hc, hn]
  refine ⟨n, ?_⟩
  rw [← hsize]
  exact card_dvd_of_surjective (plusImageMap K L T z v hL hz _
    (le_sup_right.trans le_sup_left)) (plusImageMap_surjective K L T z v hL hz _ _)

/-- Movement of z prevents the two-perfect Lᵥ image from becoming a two-group. -/
theorem plusLv_not_isPGroup [Finite G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G)) :
    ¬ IsPGroup 2 (plusImage K L T z v hL hz (Lv L v)) := by
  let A := plusImage K L T z v hL hz (Lv L v)
  have hp : IsPPerfect 2 A :=
    (isPPerfect_embedded_pResidual 2 (L ⊓ Gv v)).of_surjective
      (plusImageMap K L T z v hL hz _ (le_sup_right.trans le_sup_left))
      (plusImageMap_surjective K L T z v hL hz _ _)
  intro htwo
  have he : (⊥ : Subgroup A) = ⊤ := hp ⊥ inferInstance (htwo.to_quotient ⊥)
  have hA : A = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    have h : (⟨a, ha⟩ : A) ∈ (⊥ : Subgroup A) := he.symm ▸ mem_top _
    exact congrArg Subtype.val (mem_bot.mp h)
  have hcentral := (plusImage_eq_bot_iff K L T z v hL hz (Lv L v)
    (le_sup_right.trans le_sup_left)).mp hA
  apply hmove
  exact hcentral.trans (centralizer_le (Set.singleton_subset_iff.mpr
    (le_conjugateSpanBy (zpowers z) (Kminus K T v ⊔ Lv L v) (mem_zpowers z))))

/-- The actual source parabolic has a basis and omitted node. The index-three
premise is derived from the genuine earlier cubic quotient and movement of z. -/
theorem exists_sourceParabolic_marking [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hlocal : K ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hLK : Lv L v ≤ K)
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    {m : ℕ} (hm : m = 3 ∨ m = 4)
    (e : plusImage K L T z v hL hz K ≃* SL(m + 1, ZMod 2)) :
    ∃ (b : Basis m) (i : Fin m),
      ((plusImage K L T z v hL hz (sourceParabolic K L T v)).subgroupOf
        (plusImage K L T z v hL hz K)).map
        (e.trans (slEquivLinear (m + 1))).toMonoidHom = minimalParabolic b i ∧
      ((plusImage K L T z v hL hz (Tv T v ⊓ K)).subgroupOf
        (plusImage K L T z v hL hz K)).map
        (e.trans (slEquivLinear (m + 1))).toMonoidHom = cutStabilizer b Set.univ := by
  let C := plusImage K L T z v hL hz K
  let A := plusImage K L T z v hL hz (Lv L v)
  let S := plusImage K L T z v hL hz (Tv T v ⊓ K)
  let P := plusImage K L T z v hL hz (sourceParabolic K L T v)
  have hAC : A ≤ C := map_mono (comap_mono hLK)
  have hSC : S ≤ C := map_mono (comap_mono inf_le_right)
  have hPA : P = A ⊔ S := sourceParabolic_plusImage K L T z v hL hz
  obtain ⟨U, hU⟩ := plusSylowIntersection K L T z v hL hz hlocal
  change (U : Subgroup C).map C.subtype = S at hU
  have hUC : (U : Subgroup C) = S.subgroupOf C := by
    rw [← hU]
    exact (comap_map_eq_self_of_injective C.subtype_injective _).symm
  have hSN : S ≤ normalizer (A : Set _) :=
    normalizes_plusImage K L T _ _ z v hL hz (le_sup_right.trans le_sup_left)
      (inf_le_left.trans hL)
  have hUN : (U : Subgroup C) ≤ normalizer (A.subgroupOf C : Set C) := by
    rw [hUC, ← subgroupOf_normalizer_eq hAC]
    exact comap_mono hSN
  have hcard : ∃ n, Nat.card (A.subgroupOf C) ∣ 3 * 2 ^ n := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv]
    exact plusLv_card_dvd K L T z v hL hz hc
  have hnot : ¬ IsPGroup 2 (A.subgroupOf C) := fun hh =>
    plusLv_not_isPGroup K L T z v hL hz hmove (hh.of_equiv (subgroupOfEquivOfLe hAC))
  have hi := normalized_cubic_join_index_of_card_dvd U (A.subgroupOf C) hUN hcard hnot
  have hPS : P.subgroupOf C = A.subgroupOf C ⊔ (U : Subgroup C) := by
    rw [hPA, subgroupOf_sup hAC hSC, hUC]
  rw [← hPS] at hi
  let E := e.trans (slEquivLinear (m + 1))
  let V : Sylow 2 (LinearGroup (m + 1)) := U.mapSurjective (f := E.toMonoidHom) E.surjective
  have hVP : (V : Subgroup (LinearGroup (m + 1))) ≤ (P.subgroupOf C).map E.toMonoidHom := by
    change (U : Subgroup C).map E.toMonoidHom ≤ _
    apply map_mono
    rw [hPS]
    exact le_sup_right
  have hindex : (V : Subgroup (LinearGroup (m + 1))).relIndex
      ((P.subgroupOf C).map E.toMonoidHom) = 3 := by
    change ((U : Subgroup C).map E.toMonoidHom).relIndex _ = _
    rw [relIndex_map_map_of_injective _ _ E.injective]
    exact hi
  obtain ⟨b, i, hP, hV⟩ := FlagRecognition.exists_minimalParabolic hm V _ hVP hindex
  refine ⟨b, i, hP, ?_⟩
  change ((S.subgroupOf C).map E.toMonoidHom) = _
  rw [← hUC]
  exact hV

/-- Once an outside actor has been constructed, the source order and Sylow
data suffice for dimension four and the actual middle node. -/
theorem middle_node_of_outside_actor [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hlocal : K ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G))
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    {m : ℕ} (hm : m = 3 ∨ m = 4)
    (e : plusImage K L T z v hL hz K ≃* SL(m + 1, ZMod 2))
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K) :
    ∃ (b : Basis m) (i : Fin m), m = 3 ∧ i.val = 1 ∧
      ((plusImage K L T z v hL hz (sourceParabolic K L T v)).subgroupOf
        (plusImage K L T z v hL hz K)).map
        (e.trans (slEquivLinear (m + 1))).toMonoidHom = minimalParabolic b i := by
  obtain ⟨b, i, hP, _⟩ := exists_sourceParabolic_marking K L T z v hL hz hlocal hLK hc hmove hm e
  have ht := (Chapter1.isSylowIn_iff.mp hlocal.2.2.1).1
  obtain ⟨hm3, hi⟩ := rankFour_of_marked_sourceParabolic K L T z v hL hz hLK hK ht hR hm e b i hP hout
  exact ⟨b, i, hm3, hi, hP⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction
