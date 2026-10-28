module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalNormalizers
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalUniqueness
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFixedSpaces
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateCentralizers

/-!
# Noncyclic intersections of natural-layer conjugates

A conjugate normalizing the layer and meeting it in a four-group is an
actual natural offender. Its commutator is its fixed plane, which the
intersection already fills. The pair therefore normalizes mutually and
commutes by 6.2.3.

For an arbitrary pair, hyperplane uniqueness leaves only an intersection
of order four. If neither conjugate normalizes the other, the fixed-space
classification and ambient centralizer control make this common plane of
field type in both layers. The field-plane core theorem, transported by
the literal conjugation maps, puts both layers in the same centralizer
core and their commutator in their intersection. This again gives mutual
normalization and hence commutation.

This proves the commuting_noncyclic clause of LocalAnalysis. Its remaining
central-omega, plane-uniqueness, extraspecial-pair and order-eight assertions
remain with qt-d-1222-recognition-local-analysis. Final identification is
owned by qt-d-1222-rankone-recognition-identification.

Source: Aschbacher--Smith, 6.2.4(1) and 6.2.5(5), printed pp.680--681.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem corank_le_two_of_card {B U : Subgroup G}
    (hUB : U ≤ B) (hB : Nat.card B = 16) (hU : 4 ≤ Nat.card U) :
    ChapterE.subgroupCorank B U ≤ 2 := by
  have hc := (U.subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hUB).toEquiv, hB] at hc
  have hi : U.relIndex B ≤ 4 := by
    change Nat.card U * U.relIndex B = 16 at hc
    nlinarith
  exact (Nat.log_mono_right hi).trans (by decide : Nat.log 2 4 ≤ 2)

private theorem commuting_noncyclic_in_sylow
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (g : G) (hg : (layer L R).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (hcard : 4 ≤ Nat.card (layer L R ⊓
      (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    ⁅layer L R, (layer L R).map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  let := h.layer_elementary
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hAN : A ≤ normalizer (B : Set G) := hg.trans h.sylow_normalizes_layer
  by_contra hnon
  have hnon' : ¬ A ≤ centralizer (B : Set G) := by
    intro hc
    exact hnon (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))
  have hIF : B ⊓ A ≤ B ⊓ centralizer (A : Set G) :=
    le_inf inf_le_left (inf_le_right.trans A.le_centralizer)
  have hfixed : ChapterE.subgroupCorank B (B ⊓ centralizer (A : Set G)) ≤ n := by
    rw [hnatural.1]
    exact corank_le_two_of_card inf_le_left hnatural.2.1.card
      (hcard.trans (card_le_of_le hIF))
  have hforward := conjugate_action_corank_eq_of_natural h hnat hE
    (natural_layer_rank_bounds h hnat hE).2.2 g hAN hnon'
  have hoff : IsOffender (ChapterE.automizerRepresentation B)
      (ChapterE.inducedAutomizer B A) := by
    refine ⟨⟨?_, ChapterE.inducedAutomizer_elementary _ _ hAN⟩, ?_⟩
    · exact fun he => hnon' ((ChapterE.inducedAutomizer_eq_bot_iff hAN).mp he)
    · rw [ChapterE.fixedCodim_inducedAutomizer _ _ hAN,
        ChapterE.rank_inducedAutomizer _ _ hAN, hforward]
      exact hfixed
  obtain ⟨hfix, hcomm⟩ :=
    ((naturalOffenderFixedLines_of_natural h hnat hE) A inferInstance hAN hoff).2 hg
  have hIZ : B ⊓ A ≤ ZS (T : Subgroup G) L R := hIF.trans_eq hfix
  have hIZeq : B ⊓ A = ZS (T : Subgroup G) L R :=
    eq_of_le_of_card_ge hIZ (by rw [(h.natural_ZS_geometry hnatural).2.1]; exact hcard)
  have hmut : B ≤ normalizer (A : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr
      (hcomm.le.trans (hIZeq.symm.le.trans inf_le_right))
  exact hnon (local_commuting_normalized h hnatural hE hfactor g hmut hAN)

/-- A noncyclic intersection and normalization in one direction already force
commutation; mutual normalization is derived from the natural offender geometry. -/
theorem local_commuting_noncyclic_of_normalizes
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (g : G)
    (hAN : (layer L R).map (MulAut.conj g).toMonoidHom ≤ normalizer (layer L R : Set G))
    (hcard : 4 ≤ Nat.card (layer L R ⊓
      (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    ⁅layer L R, (layer L R).map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  obtain ⟨c, hc, hcT⟩ := IsPGroup.exists_conj_le_sylow_of_normalized T
    (normalizer (B : Set G)) A
    (h.sylow_normalizes_layer.trans (normalizer (B : Set G)).le_normalizer)
    ((T.isPGroup'.to_le h.layer_le_T).map _) hAN
  have hcB : B.map (MulAut.conj c).toMonoidHom = B :=
    mem_normalizer_iff_map_conj_eq.mp hc
  have hcg : B.map (MulAut.conj (c * g)).toMonoidHom = A.map (MulAut.conj c).toMonoidHom :=
    (fusion_map_conj_mul B c g).symm
  have hi : B ⊓ B.map (MulAut.conj (c * g)).toMonoidHom =
      (B ⊓ A).map (MulAut.conj c).toMonoidHom := by
    rw [map_inf _ _ _ (MulAut.conj c).injective, hcB, hcg]
  have hcard' : 4 ≤ Nat.card (B ⊓ B.map (MulAut.conj (c * g)).toMonoidHom : Subgroup G) := by
    rw [hi, card_map_of_injective (MulAut.conj c).injective]
    exact hcard
  have hz := commuting_noncyclic_in_sylow h hnatural hE hfactor (c * g)
    (hcg.trans_le hcT) hcard'
  have he : (⁅B, A⁆ : Subgroup G).map (MulAut.conj c).toMonoidHom = ⊥ := by
    rw [map_commutator, hcB, ← hcg, hz]
  exact (map_eq_bot_iff_of_injective _ (MulAut.conj c).injective).mp he

/-- Source 6.2.4(1): an escaping plane is the fixed space of an actual
involutory field action on the original component quotient. -/
theorem local_escaping_plane_field
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    {U : Subgroup G} (hUB : U ≤ layer L R) (hUcard : Nat.card U = 4)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (layer L R : Set G)) :
    IsInvolutoryFieldFixedSpace L M (layer L R) U n := by
  have hnat : IsNaturalModule L (layer L R) n := hnatural.1 ▸ hnatural.2.1
  have hUne : U ≠ ⊥ := by intro he; rw [he, card_bot] at hUcard; omega
  have hcor : ChapterE.subgroupCorank (layer L R) U = n := by
    have hc := (U.subgroupOf (layer L R)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hUB).toEquiv,
      hnatural.2.1.card, hUcard] at hc
    have hi : U.relIndex (layer L R) = 4 := by
      change 4 * U.relIndex (layer L R) = 16 at hc
      omega
    simp only [ChapterE.subgroupCorank, hi, hnatural.1]
    decide
  rcases fixedSpaceAlternatives_of_natural h hnat hE U hUB hUne hcor with hC | hline | hfield
  · exact (hescape (source_ordinary_fixed_space_centralizer h hE
      (natural_layer_rank_bounds h hnat hE).1 hUne hUB hC)).elim
  · obtain ⟨l, hl, he⟩ := hline
    have hc := conjugate_line_centralizer_le_normalizer h hnat hE hnatural.2.2.2.1 1 l hl
    have hone : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [hone, map_id, map_id] at hc
    exact (hescape (he ▸ hc)).elim
  · exact hfield

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- Source 6.2.5(5): conjugates with noncyclic intersection commute.
If neither layer normalizes the other, the common plane is of field type
in both. Their actual centralizer-core inclusions give mutual normalization. -/
theorem local_commuting_noncyclic
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (g : G)
    (hcard : 4 ≤ Nat.card (layer L R ⊓
      (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    ⁅layer L R, (layer L R).map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  let := h.layer_elementary
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let I := B ⊓ A
  let J := I.map (MulAut.conj g⁻¹).toMonoidHom
  let A' := B.map (MulAut.conj g⁻¹).toMonoidHom
  change 4 ≤ Nat.card I at hcard
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map _
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  by_contra hnon
  have hnon' : ¬ A ≤ centralizer (B : Set G) := by
    intro hc
    exact hnon (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))
  have hsmall : Nat.card I < 8 := by
    by_contra hh
    have he := local_hyperplane_unique h hnatural hE g (Nat.le_of_not_gt hh)
    have hc : A ≤ centralizer (B : Set G) := he.le.trans B.le_centralizer
    exact hnon' hc
  have hIcard : Nat.card I = 4 := by
    have hcB : Nat.card B = 16 := hnatural.2.1.card
    have hd : Nat.card I ∣ 2 ^ 4 := by
      have hd := card_dvd_of_le (show I ≤ B from inf_le_left)
      rw [hcB] at hd
      exact hd
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    interval_cases k <;> norm_num only [Nat.reducePow] at he <;> omega
  have hIne : I ≠ ⊥ := by intro he; rw [he, card_bot] at hIcard; omega
  have hJI : J = B ⊓ A' := by
    change (B ⊓ B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective, fusion_map_conj_inverse]
    exact inf_comm _ _
  have hJcard : Nat.card J = 4 :=
    (card_map_of_injective (MulAut.conj g⁻¹).injective).trans hIcard
  have hJne : J ≠ ⊥ := by intro he; rw [he, card_bot] at hJcard; omega
  have hJG : J.map (MulAut.conj g).toMonoidHom = I := by
    simpa only [J, inv_inv] using fusion_map_conj_inverse I g⁻¹
  have hAN : ¬ A ≤ normalizer (B : Set G) := by
    intro hN
    exact hnon (local_commuting_noncyclic_of_normalizes h hnatural hE hfactor g hN hcard)
  have hA'N : ¬ A' ≤ normalizer (B : Set G) := by
    intro hN
    have hc := local_commuting_noncyclic_of_normalizes h hnatural hE hfactor g⁻¹ hN
      (by rw [← hJI, hJcard])
    exact fusion_inverse_noncentralizing hnon'
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))
  have hIescape : ¬ centralizer (I : Set G) ≤ normalizer (B : Set G) := by
    intro he
    exact hAN ((A.le_centralizer.trans (centralizer_le inf_le_right)).trans he)
  have hJescape : ¬ centralizer (J : Set G) ≤ normalizer (B : Set G) := by
    intro he
    exact hA'N ((A'.le_centralizer.trans (centralizer_le (hJI.le.trans inf_le_right))).trans he)
  have hfI := local_escaping_plane_field h hnatural hE (show I ≤ B from inf_le_left) hIcard hIescape
  have hfJ := local_escaping_plane_field h hnatural hE (hJI.le.trans inf_le_left) hJcard hJescape
  have hAcore : A ≤ (centralizer (I : Set G)).pCoreIn 2 := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom)
      (local_field_plane_core h hnat hE hfJ hJne).1
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
      Theory.Quasithin.map_centralizer, hJG] at hh
    exact hh
  have hcomm : ⁅B, A⁆ ≤ I := (commutator_mono le_rfl hAcore).trans
    (local_field_plane_core h hnat hE hfI hIne).2
  exact hnon (local_commuting_normalized h hnatural hE hfactor g
    (le_normalizer_iff_commutator_le_right.mpr (hcomm.trans inf_le_right))
    (le_normalizer_iff_commutator_le_left.mpr (hcomm.trans inf_le_left)))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
