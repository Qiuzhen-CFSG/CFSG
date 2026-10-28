module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ResidualBlock
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.NormalizedTwoGroups

/-!
# The original canonical commutator layers

A two-group mutually normalized with a two-perfect subgroup has its
commutator in the intrinsic block layer. Applied to the source canonical
U, this gives [U,L_v]=V_v, using the proved containment V_v <= [U,K_v].
Shortness and the normal-layer dichotomy identify [U,K_v] with U(K_v).
Both equalities keep the original subgroups inside G and use only the
relative Sylow placement; neither R=R_v nor an ambient Sylow is assumed.

PreferredCanonical applies both equalities to the unchanged preferred
point with nontrivial C_V(L), discharging every layer premise.
Source: Aschbacher--Smith, 12.6.13 and 12.6.18, printed pp.826--827,
combined manuscript of 1 March 2004, using C.1.7--11, pp.123--124.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]

private theorem twoGroup_commutator_le_layer (A P : Subgroup G)
    (hp : IsPPerfect 2 A) (hP : IsPGroup 2 P)
    (hAP : A ≤ normalizer (P : Set G)) (hPA : P ≤ normalizer (A : Set G)) :
    ⁅P,A⁆ ≤ (ChapterC.blockU A).map A.subtype := by
  have hc : ⁅P,A⁆ ≤ A.pCoreIn 2 := le_pCoreIn_of_normalizes
    (hP.to_le (le_normalizer_iff_commutator_le_left.mp hAP))
    (le_normalizer_iff_commutator_le_right.mp hPA)
    (normalizer_commutator_ge_right P A)
  rw [ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype]
  exact (commutator_isPPerfect_idempotent A P hp hP hAP).symm.le.trans
    (commutator_mono hc le_rfl)

private theorem layer_fully_moved (A : Subgroup G) (hp : IsPPerfect 2 A) :
    ⁅(ChapterC.blockU A).map A.subtype,A⁆ = (ChapterC.blockU A).map A.subtype := by
  have hh := commutator_isPPerfect_idempotent A (A.pCoreIn 2) hp
    (isPGroup_pCoreIn 2 A)
    (A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  simpa only [ChapterC.blockU,pCoreIn,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hh

variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The canonical module restricts to the original moved five-space. -/
theorem SourceHypothesis.nonsingular_canonical_local_commutator
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hshort : ChapterC.IsShort L)
    (S : Sylow 2 (Gv (v : G)))
    (hRN : R L (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) (v : G) ≤
      normalizer (Lv L (v : G) : Set G))
    (hred : U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) =
      (reducedTwoSubgroup (Kv (v : G) ⊔
        (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)).map
          (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G).subtype)
    (hm : Vv L V (v : G) ≤ ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype),Kv (v : G)⁆) :
    ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype),Lv L (v : G)⁆ =
      Vv L V (v : G) := by
  let C := Kv (v : G)
  let P := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := C ⊔ P
  let E := U C P
  change E = (reducedTwoSubgroup J).map J.subtype at hred
  have hJE : J ≤ normalizer (E : Set G) := by
    rw [hred]
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (reducedTwoSubgroup J).le_normalizer_map J.subtype
  have hE2 : IsPGroup 2 E := by
    rw [hred]
    exact (pCore_isPGroup.to_le (reducedPSubgroup_le_pCore 2 J)).map J.subtype
  have hER : E ≤ R L C P (v : G) := by
    rw [hred]
    exact (map_mono (reducedPSubgroup_le_pCore 2 J)).trans (core_le_R_of_sylow L C _ S (Kv_le_Gv _))
  have hAE : Lv L (v : G) ≤ normalizer (E : Set G) :=
    (H.nonsingular_canonical_component D v hv).2.1.trans (le_sup_left.trans hJE)
  have hWE : Vv L V (v : G) ≤ E := hm.trans
    (le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hJE))
  apply le_antisymm
  · exact (twoGroup_commutator_le_layer (Lv L (v : G)) E
      (isPPerfect_embedded_pResidual 2 (CLv L (v : G))) hE2 hAE (hER.trans hRN)).trans_eq
        (H.nonsingular_local_block_layer D hshort v hv)
  · rw [←D.local_moved_generated H.chosen v hv]
    exact commutator_mono hWE le_rfl

/-- The canonical moved module is the intrinsic layer of the original K_v-block. -/
theorem SourceHypothesis.nonsingular_canonical_residual_commutator
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hshort : ChapterC.IsShort (Kv (v : G)))
    (S : Sylow 2 (Gv (v : G)))
    (hred : U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) =
      (reducedTwoSubgroup (Kv (v : G) ⊔
        (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)).map
          (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G).subtype)
    (hm : Vv L V (v : G) ≤ ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype),Kv (v : G)⁆) :
    ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype),Kv (v : G)⁆ =
      (ChapterC.blockU (Kv (v : G))).map (Kv (v : G)).subtype := by
  let C := Kv (v : G)
  let P := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := C ⊔ P
  let E := U C P
  change E = (reducedTwoSubgroup J).map J.subtype at hred
  have hJE : J ≤ normalizer (E : Set G) := by
    rw [hred]
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (reducedTwoSubgroup J).le_normalizer_map J.subtype
  have hCE : C ≤ normalizer (E : Set G) := le_sup_left.trans hJE
  have hEJ : E ≤ J := by rw [hred]; exact map_subtype_le _
  have hEC : E ≤ normalizer (C : Set G) := hEJ.trans
    ((sup_le (Kv_le_Gv _) (map_subtype_le _)).trans
      ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv _)).mp (Kv_normalIn_Gv _)))
  have hE2 : IsPGroup 2 E := by
    rw [hred]
    exact (pCore_isPGroup.to_le (reducedPSubgroup_le_pCore 2 J)).map J.subtype
  apply le_antisymm (twoGroup_commutator_le_layer C E hshort.twoPerfect hE2 hCE hEC)
  rcases hshort.blockU_le_or_centralizes_of_normalizing_twoGroup hE2 hCE hEC with hu | hc
  · rw [←layer_fully_moved C hshort.twoPerfect]
    exact commutator_mono hu le_rfl
  · have hW : Vv L V (v : G) = ⊥ := bot_unique
      (hm.trans_eq (commutator_eq_bot_iff_le_centralizer.mpr hc))
    have hcard := D.nonsingular_moved_card H.chosen v hv
    rw [hW,card_bot] at hcard
    norm_num at hcard

end CFSG.Quasithin.Chapter12.Section06
