module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.Primitive
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.Action
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Cartan
public import CFSG.Quasithin.ChapterE.GenerationKnownSimple
public import CFSG.Quasithin.ChapterE.Section02.Structure.ThreeHallGeneration

/-!
# The exterior generation-two and Hall-three conclusion

This proves the Hall step in Lemma 12.5.12. Positivity is obtained from
the actual nontrivial chosen module and the KnownSimple E-generation source;
the minimum is then attained before the hypothesis `n(H) ≠ 1` is used.  The
E.2.2 construction supplies the actual Borel Hall subgroup on the literal
overlap.  The preceding prime sieve turns it into a nontrivial 3-group, and
the general three-Hall bound gives `n(H) ≤ 2`.

The specialized A.3.15 action exclusion and Chapter 4 normalizer bound are
constructed by Hall.Action and Hall.OddNormalizer and discharged below.
The original H-star family, exterior marking and literal overlap are retained.
The earlier Structural1222At input is produced by qt-d-1222-source and
discharged by qt-d-1251-source. The generation-one exclusion comes from
WeakClosure.GenerationOne, with final fusion assembly in qt-d-1251-fusion.

Source: Aschbacher--Smith, 12.2.11(a) and 12.5.12, printed pp.798--799 and821.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  (s : SylowExteriorMarking D)

include D h s

omit h in
private theorem ambient_two_dvd_card_of_point (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    2 ∣ Nat.card H := by
  have hV : V ≠ ⊥ := D.ne_bot
  have hTV : V ≤ (T : Subgroup G) := D.le_sylow
  have hT : (T : Subgroup G) ≠ ⊥ := by
    intro hT
    apply hV
    exact bot_unique (hTV.trans (le_of_eq hT))
  obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
  have hnpos : 0 < n := by
    by_contra hn0
    have hn0' : n = 0 := Nat.eq_zero_of_not_pos hn0
    apply hT
    rw [hn0', pow_zero] at hn
    exact Subgroup.card_eq_one.mp hn
  have h2T : 2 ∣ Nat.card (T : Subgroup G) := by
    rw [hn]
    exact dvd_pow_self 2 (Nat.ne_of_gt hnpos)
  exact h2T.trans (card_dvd_of_le hH.1.1.2)

omit [Finite G] h in
private theorem exterior_hall_literal
    {H : Subgroup G} (_hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    {B : Subgroup H} (hBM : B ≤ s.marking.M.subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf (s.marking.M.subgroupOf H))) :
    let C := B.map H.subtype
    C ≤ H ⊓ s.marking.M ∧
      IsHallSubgroup oddPrimes (C.subgroupOf (H ⊓ s.marking.M)) := by
  let C := B.map H.subtype
  have hCM : C ≤ s.marking.M := map_le_iff_le_comap.mpr hBM
  have hCJ : C ≤ H ⊓ s.marking.M := le_inf (map_subtype_le _) hCM
  have hmap : (s.marking.M.subgroupOf H).map H.subtype = H ⊓ s.marking.M := by
    rw [subgroupOf_map_subtype, inf_comm]
  have hcard : Nat.card (C.subgroupOf (H ⊓ s.marking.M)) =
      Nat.card (B.subgroupOf (s.marking.M.subgroupOf H)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCJ).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv,
      card_map_of_injective H.subtype_injective]
  have hindex : (C.subgroupOf (H ⊓ s.marking.M)).index =
      (B.subgroupOf (s.marking.M.subgroupOf H)).index := by
    have hh := relIndex_map_map_of_injective B (s.marking.M.subgroupOf H)
      H.subtype_injective
    rw [hmap] at hh
    exact hh
  refine ⟨hCJ, ?_⟩
  exact ⟨fun p hp => hHall.p_in_pi_of_p_dvd_card p (hcard ▸ hp),
    fun p hp => hHall.p_in_pi_of_p_dvd_index p (hindex ▸ hp)⟩

/-- Positive attained generation on the original H-star carrier. In particular,
zero is excluded by an existence theorem, not by the numerical infimum alone. -/
theorem exterior_generation_spec
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    0 < ChapterE.generationParameter H ∧
      ChapterE.IsEGenerated (ChapterE.generationParameter H) H := by
  have hgen_exists := ChapterE.source_generation_exists_knownSimple
    (Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1) (T.subtype hH.1.1.2)
  exact ChapterE.generationParameter_spec
    (fun hodd => hodd.not_two_dvd_nat
      (ambient_two_dvd_card_of_point (D := D) (s := s) H hH)) hgen_exists

/-- Modular 12.5.12 deduction with the two specialized source inputs explicit.
The endpoint below supplies their proved constructors. -/
theorem exterior_generation_two_and_hall_three_of_controls
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1)
    (hgen_ne_one : ChapterE.generationParameter H ≠ 1)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    (control : ExteriorOddNormalizerControl s) :
    ChapterE.generationParameter H = 2 ∧
      ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ H ⊓ s.marking.M ∧
        IsHallSubgroup oddPrimes (C.subgroupOf (H ⊓ s.marking.M)) ∧
        IsPGroup 3 C := by
  have hspec := exterior_generation_spec D h s hH
  have hpos : 0 < ChapterE.generationParameter H := hspec.1
  have hlarge : 1 < ChapterE.generationParameter H := by omega
  let F := D.fundamentalSetup h.toHypothesis1221
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) F.maximalLocal := by
    change H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (Chapter3.Section02.localOrbit T L : Set G))
    simpa only [D.localOrbit_eq, ExteriorMarking.M] using hH
  obtain ⟨hP, f, _hf, hbound, d, hmax, _hperm, _hescape⟩ :=
    Chapter10.source_hstar_cartan_data_of_generation_gt_one F hH' hlarge
  have hFmax : F.maximalLocal = s.marking.M := by
    change normalizer (Chapter3.Section02.localOrbit T L : Set G) =
      normalizer (L : Set G)
    rw [D.localOrbit_eq]
  have hBM : d.witness.abelianGroup ≤ s.marking.M.subgroupOf H := by
    rw [← hFmax]
    exact hmax ▸ d.hall_le
  have hHallM : IsHallSubgroup oddPrimes
      (d.witness.abelianGroup.subgroupOf (s.marking.M.subgroupOf H)) := by
    rw [← hFmax]
    exact hmax ▸ d.hall
  let C := d.witness.abelianGroup.map H.subtype
  have hCJ : C ≤ H ⊓ s.marking.M :=
    (exterior_hall_literal D s hH hBM hHallM).1
  have hHallC : IsHallSubgroup oddPrimes (C.subgroupOf (H ⊓ s.marking.M)) :=
    (exterior_hall_literal D s hH hBM hHallM).2
  have hB3 : IsPGroup 3 d.witness.abelianGroup :=
    exterior_hall_three_of_controls s h structural action control hH hHGi hlarge hP d
      (hmax.trans (congrArg (fun M : Subgroup G => M.subgroupOf H) hFmax))
  have hC3 : IsPGroup 3 C := hB3.of_equiv
    (d.witness.abelianGroup.equivMapOfInjective H.subtype H.subtype_injective)
  have hupper : ChapterE.generationParameter H ≤ 2 :=
    ChapterE.generationParameter_le_two_of_three_hall
      (Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1)
      (T.subtype hH.1.1.2) hP d.witness.abelianGroup d.hall_le d.hall hB3
  have hCne : C ≠ ⊥ := by
    intro hC
    have hB : d.witness.abelianGroup ≠ ⊥ := by
      intro hB
      have hcyc : Nat.card d.witness.cyclicGroup ≤ 1 := by
        calc
          Nat.card d.witness.cyclicGroup ≤ Nat.card d.witness.abelianGroup :=
            Nat.card_le_card_of_injective (inclusion d.witness.cyclic_le)
              (inclusion_injective d.witness.cyclic_le)
          _ = 1 := by rw [hB, card_bot]
      have hf2 : 2 ≤ f := by omega
      have hpow : 4 ≤ 2 ^ f := by
        exact pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hf2
      rw [d.witness.card] at hcyc
      omega
    exact hB ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp hC)
  refine ⟨Nat.le_antisymm hupper (by omega), C, hCne, hCJ, hHallC, hC3⟩

/-- The specialized 12.2.11(a) prime exclusion on the actual E.2.2 Borel
Hall subgroup. Both the action and odd-normalizer inputs are constructed. -/
theorem exterior_hall_three
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1)
    (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H) :
    IsPGroup 3 d.witness.abelianGroup :=
  exterior_hall_three_of_controls s h structural
    (exterior_odd_action_centralizes s) (exterior_oddNormalizer_control s h)
    hH hHGi hlarge hP d hmax

/-- Lemma 12.5.12 on the original exterior marking, using the preceding
generation-one exclusion. The nontrivial odd Hall subgroup is embedded in G,
with Hall index measured in the literal H ∩ M. The earlier structural input
retains its producer qt-d-1222-source and final owner qt-d-1251-source. -/
theorem exterior_generation_two_and_hall_three
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1)
    (hgen_ne_one : ChapterE.generationParameter H ≠ 1)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    ChapterE.generationParameter H = 2 ∧
      ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ H ⊓ s.marking.M ∧
        IsHallSubgroup oddPrimes (C.subgroupOf (H ⊓ s.marking.M)) ∧
        IsPGroup 3 C :=
  exterior_generation_two_and_hall_three_of_controls D h s hH hHGi hgen_ne_one
    structural (exterior_odd_action_centralizes s) (exterior_oddNormalizer_control s h)

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
