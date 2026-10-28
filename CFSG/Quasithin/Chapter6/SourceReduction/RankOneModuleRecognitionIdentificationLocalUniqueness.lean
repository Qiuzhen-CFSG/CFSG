module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosureRanksGlobal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionCorank

/-!
# Hyperplane rigidity for the source natural layer

The global-r bound and the local natural-action calculation identify the
ambient centralizer of every subgroup of order at least eight with that of
the sixteen-element layer. The two-core of that centralizer contains the
layer and is normalized by the uniqueness subgroup in E.6.1. Consequently
its normalizer lies in M. A common hyperplane therefore forces the original
conjugator into M, where the relative TI property makes the layers equal.

Transporting the centralizer identity to each conjugate also shows that
mutual normalizer intersections of index two act nontrivially. This is the
first action exclusion in 6.2.6; no extraspecial-pair conclusion is assumed.
The Chapter 12 companion supplies the E.6.1 premises for the original layer.

Source: Aschbacher--Smith, 6.1.10(1), 6.2.5(6), and the first paragraph of
6.2.6, printed pp.670 and 681.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

private theorem normalizer_centralizer_le
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L R)) :
    normalizer (centralizer (layer L R : Set G) : Set G) ≤ M := by
  let B := layer L R
  let C := centralizer (B : Set G)
  let Q := C.pCoreIn 2
  let := hE.elementary
  have hBQ : B ≤ Q := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 B) B.le_centralizer (Subgroup.centralizer_le_normalizer _)
  have hQN := normalizer_le_normalizer_characteristic_image C (pCore 2 C)
  apply hQN.trans
  apply normalizer_le_of_unique_maximalTwoLocal hE.unique (isPGroup_pCoreIn 2 C)
  · intro he
    exact hE.nontrivial (bot_unique (hBQ.trans_eq he))
  · exact (inf_le_left.trans inf_le_right).trans
      ((normalizer_le_normalizer_centralizer B).trans hQN)

omit [Finite G] in
private theorem corank_lt_two_of_card {B U : Subgroup G}
    (hUB : U ≤ B) (hB : Nat.card B = 16) (hU : 8 ≤ Nat.card U) :
    ChapterE.subgroupCorank B U < 2 := by
  have hc := (U.subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hUB).toEquiv, hB] at hc
  have hi : U.relIndex B ≤ 2 := by
    change Nat.card U * U.relIndex B = 16 at hc
    nlinarith
  change Nat.log 2 (U.relIndex B) < 2
  exact lt_of_le_of_lt (Nat.log_mono_right hi) (by decide : Nat.log 2 2 < 2)

/-- A hyperplane has the same full ambient centralizer as the natural layer. -/
theorem local_large_subgroup_centralizer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    {U : Subgroup G} (hUB : U ≤ layer L R) (hU : 8 ≤ Nat.card U) :
    centralizer (U : Set G) = centralizer (layer L R : Set G) := by
  have hnat : IsNaturalModule L (layer L R) n := hnatural.1 ▸ hnatural.2.1
  let := h.layer_elementary
  have hsmall : ChapterE.subgroupCorank (layer L R) U < n := by
    rw [hnatural.1]
    exact corank_lt_two_of_card hUB (by simpa using hnatural.2.1.card) hU
  have hC := natural_local_centralizer_eq_of_corank_lt hnat
    (hE.normalizer_le.trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal))
    hE hUB hsmall
  have hbound := (natural_layer_rank_bounds h hnat hE).1
  have hCM : centralizer (U : Set G) ≤ M :=
    (ChapterE.centralizer_le_normalizer_of_corank_lt_globalR hUB
      (lt_of_lt_of_le (by exact_mod_cast hsmall) hbound)).trans hE.normalizer_le
  rwa [inf_eq_right.mpr hCM, inf_eq_right.mpr hE.centralizer_le] at hC

/-- Source 6.2.5(6), using centralizer rigidity and the original uniqueness subgroup. -/
theorem local_hyperplane_unique
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (g : G)
    (hcard : 8 ≤ Nat.card (layer L R ⊓
      (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    (layer L R).map (MulAut.conj g).toMonoidHom = layer L R := by
  let B := layer L R
  let I := B ⊓ B.map (MulAut.conj g).toMonoidHom
  let J := I.map (MulAut.conj g⁻¹).toMonoidHom
  have hJB : J ≤ B := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      (show I ≤ B.map (MulAut.conj g).toMonoidHom from inf_le_right)
    rwa [fusion_map_conj_inverse] at hh
  have hJcard : 8 ≤ Nat.card J := by
    change 8 ≤ Nat.card (I.map (MulAut.conj g⁻¹).toMonoidHom)
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hcard
  have hCI := local_large_subgroup_centralizer h hnatural hE (show I ≤ B from inf_le_left) hcard
  have hCJ := local_large_subgroup_centralizer h hnatural hE hJB hJcard
  have hJI : J.map (MulAut.conj g).toMonoidHom = I := by
    simpa only [J, inv_inv] using fusion_map_conj_inverse I g⁻¹
  have hCg : (centralizer (B : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer (B : Set G) := by
    rw [← hCJ, Theory.Quasithin.map_centralizer, hJI, hCI]
    exact hCJ.symm
  have hgM : g ∈ M := normalizer_centralizer_le hE
    (mem_normalizer_iff_map_conj_eq.mpr hCg)
  rcases hE.ti g hgM with he | he
  · rw [he, card_bot] at hcard
    omega
  · exact he

/-- The large-subgroup centralizer identity transported to an arbitrary conjugate. -/
theorem local_conjugate_large_subgroup_centralizer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (g : G) {U : Subgroup G}
    (hUB : U ≤ (layer L R).map (MulAut.conj g).toMonoidHom)
    (hU : 8 ≤ Nat.card U) :
    centralizer (U : Set G) =
      centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G) := by
  have hback : U.map (MulAut.conj g⁻¹).toMonoidHom ≤ layer L R := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hUB
    rwa [fusion_map_conj_inverse] at hh
  have hcard : 8 ≤ Nat.card (U.map (MulAut.conj g⁻¹).toMonoidHom) := by
    rwa [card_map_of_injective (MulAut.conj g⁻¹).injective]
  have he := local_large_subgroup_centralizer h hnatural hE hback hcard
  have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) he
  have hu : (U.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = U := by
    simpa only [inv_inv] using fusion_map_conj_inverse U g⁻¹
  rwa [Theory.Quasithin.map_centralizer, hu, Theory.Quasithin.map_centralizer] at hh

/-- The index-two normalizer intersection acts nontrivially on the other layer.
This removes the trivial-action case at the start of source 6.2.6. -/
theorem local_pair_normalizer_action_nontrivial
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (g : G)
    (hleft : (layer L R ⊓ normalizer
      ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)).relIndex (layer L R) = 2)
    (hright : ((layer L R).map (MulAut.conj g).toMonoidHom ⊓
      normalizer (layer L R : Set G)).relIndex
        ((layer L R).map (MulAut.conj g).toMonoidHom) = 2) :
    ¬ (layer L R).map (MulAut.conj g).toMonoidHom ⊓ normalizer (layer L R : Set G) ≤
      centralizer (layer L R : Set G) := by
  let A := (layer L R).map (MulAut.conj g).toMonoidHom ⊓
    normalizer (layer L R : Set G)
  have hAB : A ≤ (layer L R).map (MulAut.conj g).toMonoidHom := inf_le_left
  have hc := (A.subgroupOf ((layer L R).map (MulAut.conj g).toMonoidHom)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hAB).toEquiv,
    card_map_of_injective (MulAut.conj g).injective, hnatural.2.1.card] at hc
  change Nat.card A * A.relIndex ((layer L R).map (MulAut.conj g).toMonoidHom) = 16 at hc
  rw [hright] at hc
  have hA : 8 ≤ Nat.card A := by omega
  have hC := local_conjugate_large_subgroup_centralizer h hnatural hE g hAB hA
  intro ha
  have hB : layer L R ≤ normalizer
      ((layer L R).map (MulAut.conj g).toMonoidHom : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    rw [← hC]
    exact le_centralizer_iff.mp ha
  rw [inf_eq_left.mpr hB, relIndex_self] at hleft
  contradiction

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
