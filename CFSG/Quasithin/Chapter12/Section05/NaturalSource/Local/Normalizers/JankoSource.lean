module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoMax2Actor
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoActorSeed
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoReverseLocal
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.FullSylowExclusions
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.CoverAssembly

/-!
# Completing all native rows of the original Janko normalizer argument

The original point parabolic has nontrivial two-core and contains the full
component Sylow. The named native cover places it in one of four locals.
The first-centralizer obstruction and the linear-five order exclude two
rows. The surviving max1/max4 placements provide a nonzero normal seed for
the same original projected actor, so the cover also applies to that actor.

The four max1/max4 comparisons, the marked max2 cubic-kernel argument,
and the full-Sylow exclusion in max3 now settle every actor row. Native
conjugators change the supplied component equivalence simultaneously for
all original subgroups. The original source alternatives then give both
G3,G6 <= N_G(L), with no remaining placement or action callback.

The explicit MaximalTwoLocalCover input is owned by
qt-model-j4-elementary-normalizer-cover. It must be discharged before this
is an unconditional source theorem; qt-d-1251-local retains that assembly,
and qt-d-1251-source retains final exterior assembly.
Source: Aschbacher--Smith 12.5.3--4, printed pp.818--819/PDF pp.835--836.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
open Janko4.LocalStructure
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

private theorem map_le_conjugate_pull {C : Type*} [Group C]
    (e : C ≃* Janko4.Model) (H : Subgroup C) (N : Subgroup Janko4.Model) (a : Janko4.Model)
    (h : H.map e.toMonoidHom ≤ N.map (MulAut.conj a).toMonoidHom) :
    H.map (e.trans (MulAut.conj a).symm).toMonoidHom ≤ N := by
  let c := MulAut.conj a
  have hc : c.symm.toMonoidHom.comp c.toMonoidHom = MonoidHom.id Janko4.Model := by
    ext x
    exact c.symm_apply_apply x
  have hh := map_mono (f := c.symm.toMonoidHom) h
  change (H.map e.toMonoidHom).map c.symm.toMonoidHom ≤
    (N.map c.toMonoidHom).map c.symm.toMonoidHom at hh
  change H.map (c.symm.toMonoidHom.comp e.toMonoidHom) ≤ N
  simpa only [map_map, hc, map_id] using hh

private theorem map_le_firstCentralizer {C : Type*} [Group C]
    (e : C ≃* Janko4.Model) (H : Subgroup C)
    (hH : H.map e.toMonoidHom ≤ sourceSubgroup) :
    H.map (e.trans (MulAut.conj
      Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.h⁻¹)).toMonoidHom ≤
        Janko4.InvolutionCentralizers.First.centralizer := by
  have hh := map_mono (f := (MulAut.conj
    Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.h⁻¹).toMonoidHom) hH
  rw [NativeCoverTransport.sourceSubgroup_map_conj_firstCentralizer, map_map] at hh
  exact hh

private theorem native_cover_of_core (cover : LargeCenterRadicals.MaximalTwoLocalCover)
    (J : Subgroup Janko4.Model) (hc : pCore 2 J ≠ ⊥) :
    ∃ g : Janko4.Model,
      J ≤ ElementaryNormalizerCover.max1.map (MulAut.conj g).toMonoidHom ∨
      J ≤ sourceSubgroup.map (MulAut.conj g).toMonoidHom ∨
      J ≤ LinearFive.fullNormalizer.map (MulAut.conj g).toMonoidHom ∨
      J ≤ SymmetricLinear.max4Subgroup.map (MulAut.conj g).toMonoidHom := by
  have ht : IsTwoLocal (normalizer (J.pCoreIn 2 : Set Janko4.Model)) := by
    refine ⟨J.pCoreIn 2, ?_, pCore_isPGroup.map J.subtype, rfl⟩
    intro hz
    exact hc ((map_eq_bot_iff_of_injective _ J.subtype_injective).mp hz)
  obtain ⟨M,hM,hm⟩ := ht.exists_le_maximal
  have hJM : J ≤ M := (J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J))).trans hM
  obtain ⟨g,hg | hg | hg | hg⟩ := cover M hm
  · exact ⟨g, .inl (hJM.trans_eq hg)⟩
  · exact ⟨g, .inr (.inl (hJM.trans_eq hg))⟩
  · exact ⟨g, .inr (.inr (.inl (hJM.trans_eq hg)))⟩
  · exact ⟨g, .inr (.inr (.inr (hJM.trans_eq hg)))⟩

theorem pointComponentParabolic_native_pair_of_cover
    (cover : LargeCenterRadicals.MaximalTwoLocalCover)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model) :
    ∃ a : s.pointCoreImage K ≃* Janko4.Model,
      (s.pointComponentParabolic K).map a.toMonoidHom ≤ ElementaryNormalizerCover.max1 ∨
      (s.pointComponentParabolic K).map a.toMonoidHom ≤ SymmetricLinear.max4Subgroup := by
  have hY := s.Y_le_point_component_of_large_model h hK hN
    (.inr (.inr ⟨(s.pointComponentCoreEquivImage hK.1 hN).trans e⟩))
  obtain ⟨S,hSP,_⟩ := s.pointComponentParabolic_sylow_index hK.1 hN hLK hY
  have h32 : 32 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 5) (by
    rw [Nat.card_congr e.toEquiv, Janko4.Cardinality.model_card]
    decide)
  have hc := s.pointComponentParabolic_core_ne_bot S hSP h32
  let P := (s.pointComponentParabolic K).map e.toMonoidHom
  have hcP : pCore 2 P ≠ ⊥ := by
    intro hz
    let a := e.subgroupMap (s.pointComponentParabolic K)
    have ha := pCore_map_iso 2 a
    change (pCore 2 (s.pointComponentParabolic K)).map a.toMonoidHom = pCore 2 P at ha
    rw [hz] at ha
    exact hc ((map_eq_bot_iff_of_injective _ a.injective).mp ha)
  obtain ⟨g,hg | hg | hg | hg⟩ := native_cover_of_core cover P hcP
  · exact ⟨e.trans (MulAut.conj g).symm, .inl (map_le_conjugate_pull e _ _ g hg)⟩
  · have ht := map_le_firstCentralizer (e.trans (MulAut.conj g).symm) _
      (map_le_conjugate_pull e _ _ g hg)
    exact (s.pointComponentParabolic_not_janko_firstCentralizer h hK hLK hN _ ht).elim
  · let a := e.trans (MulAut.conj g).symm
    have ht := map_le_conjugate_pull e _ _ g hg
    exact (LinearFive.not_sylow_le_fullNormalizer
      (S.mapSurjective (f := a.toMonoidHom) a.surjective) ((map_mono hSP).trans ht)).elim
  · exact ⟨e.trans (MulAut.conj g).symm, .inr (map_le_conjugate_pull e _ _ g hg)⟩

theorem local_normalizer_le_M_of_janko_native_cover
    (cover : LargeCenterRadicals.MaximalTwoLocalCover)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (i : ℕ) (hi : i = 3 ∨ i = 6) : s.marking.Gi i ≤ s.marking.M := by
  obtain ⟨a,ha⟩ := s.pointComponentParabolic_native_pair_of_cover cover h hK hLK hN e
  have hc := (s.point_projection_janko_elementary_seed h hK hN a ha i hi).2.1
  obtain ⟨g,hg | hg | hg | hg⟩ := native_cover_of_core cover _ hc
  · rcases ha with ha | ha
    · exact s.local_normalizer_le_M_of_janko_conjugate_max1 h hK hLK hN a ha i hi g hg
    · exact s.local_normalizer_le_M_of_janko_max4_conjugate_max1 h hK hLK hN a ha i hi g hg
  · exact s.local_normalizer_le_M_of_janko_max2 h hK hLK hN _ i hi
      (map_le_firstCentralizer (a.trans (MulAut.conj g).symm) _
        (map_le_conjugate_pull a _ _ g hg))
  · let b := a.trans (MulAut.conj g).symm
    have ht := map_le_conjugate_pull a _ _ g hg
    obtain ⟨S,_,hSA⟩ := s.point_projection_contains_original_sylow hN i hi
    exact (LinearFive.not_sylow_le_fullNormalizer
      (S.mapSurjective (f := b.toMonoidHom) b.surjective) ((map_mono hSA).trans ht)).elim
  · rcases ha with ha | ha
    · exact s.local_normalizer_le_M_of_janko_max1_conjugate_max4 h hK hLK hN a ha i hi g hg
    · exact s.local_normalizer_le_M_of_janko_conjugate_max4 h hK hLK hN a ha i hi g hg

theorem local_normalizer_le_M_from_native_cover
    (cover : LargeCenterRadicals.MaximalTwoLocalCover)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (i : ℕ) (hi : i = 3 ∨ i = 6) : s.marking.Gi i ≤ s.marking.M := by
  by_contra he
  obtain ⟨K,hK,hLK,hN,⟨e⟩,_⟩ :=
    s.exists_janko_point_projection_of_local_normalizer_escape h i hi he
  exact he (s.local_normalizer_le_M_of_janko_native_cover cover h hK hLK hN
    ((s.pointComponentCoreEquivImage hK.1 hN).symm.trans e) i hi)

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
