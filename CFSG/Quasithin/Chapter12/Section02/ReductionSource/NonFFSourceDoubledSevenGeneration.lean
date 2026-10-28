module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSevenCentralizers
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSevenGeneration
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryGeneration
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Transport
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Cartan

/-!
# The full A₇ Cartan bound on the original chosen orbit

The original marking identifies the whole ambient automizer with S₇,
so its literal E.3.37 parameter is at most two. The actual H-star Hall-Cartan
construction retains its prescribed Sylow and reflected normalizer escape.
If its cyclic subgroup had a nontrivial action kernel, a prime-order
subgroup of that kernel would contradict original odd-normalizer control.
Faithful transport therefore gives n(H) ≤ 2 and then w ≤ 2, using the
already proved r ≥ 4 on the same original orbit.

Only the original odd-normalizer premise remains explicit; this is not
a completed proof of 7.3.4 or of the A₇ exclusion. The rank comparison is
reused from the doubled-binary module because it is independent of that
row's marking, and the overlap transport is likewise model independent.
Source: Aschbacher--Smith E.3.35--39, 4.4.3 and 7.3.4, pp.238--240,619,699.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE
open ChapterE.Section06.FixedPointBounds ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.AlternatingSevenConjugatePair.Model
open Chapter7.NormalizedSource.MathieuGeneration
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The full actual automizer satisfies the table's Cartan upper bound. -/
theorem sourceOrbit_seven_nPrime_le_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ)) :
    nPrime (Automizer D.sourceOrbit) ≤ 2 := by
  obtain ⟨C⟩ := D.sourceOrbit_seven_action_coordinates h hd σ hσ hmodel
  rw [nPrime_eq_of_mulEquiv C.automizer]
  exact doubledSeven_nPrime_le_two

/-- Original odd-normalizer control makes the actual H-star Cartan action faithful. -/
theorem sourceOrbit_seven_generation_le_two_of_odd_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (hodd : ∀ X : Subgroup G, X ≠ ⊥ →
      X ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) →
      Odd (Nat.card X) → normalizer (X : Set G) ≤ normalizer (L : Set G))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    generationParameter H ≤ 2 := by
  by_cases hsmall : generationParameter H ≤ 1
  · omega
  have hlarge : 1 < generationParameter H := by omega
  let S := D.fundamentalSetup h.toHypothesis1221
  have hSM : S.maximalLocal = normalizer (L : Set G) := by
    change normalizer (Chapter3.Section02.localOrbit T L : Set G) = _
    rw [D.localOrbit_eq]
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) S.maximalLocal := hSM.symm ▸ hH
  obtain ⟨hP,f,_,hf,d,he,_,hescape⟩ :=
    Chapter10.source_hstar_cartan_data_of_generation_gt_one S hH' hlarge
  have he' : ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H := by simpa only [hSM] using he
  have hBM : d.witness.cyclicGroup.map H.subtype ≤ normalizer (L : Set G) :=
    map_le_iff_le_comap.mpr (d.witness.cyclic_le.trans (d.hall_le.trans_eq he'))
  have hfaith : d.witness.cyclicGroup.map H.subtype ⊓
      centralizer (D.sourceOrbit : Set G) = ⊥ := by
    by_contra hn
    let K := d.witness.cyclicGroup ⊓ (centralizer (D.sourceOrbit : Set G)).subgroupOf H
    have hK : K ≠ ⊥ := by
      intro hb
      apply hn
      apply bot_unique
      rintro x ⟨⟨y,hy,hxy⟩,hx⟩
      have hyK : y ∈ K := ⟨hy, by
        change H.subtype y ∈ centralizer (D.sourceOrbit : Set G)
        exact Eq.mpr (congrArg (fun z : G => z ∈ centralizer (D.sourceOrbit : Set G)) hxy) hx⟩
      have hy1 : y = 1 := mem_bot.mp (hb ▸ hyK)
      rw [← hxy,hy1]
      exact one_mem _
    have hKo : Odd (Nat.card K) := d.witness.odd.of_dvd_nat
      (card_dvd_of_le (show K ≤ d.witness.abelianGroup from inf_le_left.trans d.witness.cyclic_le))
    obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd (fun hc => hK (card_eq_one.mp hc))
    let : Fact p.Prime := ⟨hp⟩
    have hpo : Odd p := hKo.of_dvd_nat hpd
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' p hpd
    let A : Subgroup H := zpowers (x : H)
    have hAK : A ≤ K := zpowers_le.mpr x.property
    have hAc : A ≤ d.witness.cyclicGroup := hAK.trans inf_le_left
    have hcard : Nat.card A = p := by
      rw [Nat.card_zpowers,Subgroup.orderOf_coe,hx]
    have hAp : IsPGroup p A := IsPGroup.of_card (n := 1) (by simpa using hcard)
    have hmcard : Nat.card (A.map H.subtype) = p :=
      (card_map_of_injective H.subtype_injective).trans hcard
    have hne : A.map H.subtype ≠ ⊥ := by
      intro hb
      rw [hb,card_bot] at hmcard
      exact hp.ne_one hmcard.symm
    have hle : A.map H.subtype ≤ normalizer (L : Set G) ⊓
        centralizer (D.sourceOrbit : Set G) :=
      le_inf ((map_mono hAc).trans hBM) (map_le_iff_le_comap.mpr (hAK.trans inf_le_right))
    have hN := hodd (A.map H.subtype) hne hle (hmcard.symm ▸ hpo)
    exact hescape p inferInstance A hpo hAc hAp
      (inf_le_right.trans (hN.trans_eq hSM.symm))
  let w := overlapWitness hH.1.1.2 D.sylow_normalizes_component d he'
  obtain ⟨C⟩ := D.sourceOrbit_seven_action_coordinates h hd σ hσ hmodel
  apply hf.trans (doubledSeven_faithful_cartan_bound D.sourceOrbit (normalizer (L : Set G))
    (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).symm C.automizer w ?_)
  exact (congrArg (fun X : Subgroup G => X ⊓ centralizer (D.sourceOrbit : Set G))
    (overlapWitness_cyclic_image hH.1.1.2 D.sylow_normalizes_component d he')).trans hfaith

/-- The outside-overgroup argument on the unchanged orbit, retaining original 4.4.3. -/
theorem sourceOrbit_seven_globalW_le_two_of_odd_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (hodd : ∀ X : Subgroup G, X ≠ ⊥ →
      X ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) →
      Odd (Nat.card X) → normalizer (X : Set G) ≤ normalizer (L : Set G)) :
    globalW D.sourceOrbit T ≤ 2 := by
  obtain ⟨H,hH⟩ := D.doubledOrbit_outside_of_many h hmany
  have hb := D.sourceOrbit_doubled_min_parameters_le_generation h hd hH
  have hg : (generationParameter H : ℕ∞) ≤ 2 := by
    exact_mod_cast D.sourceOrbit_seven_generation_le_two_of_odd_control h hd σ hσ hmodel hodd hH
  have hr : (2 : ℕ∞) < globalR D.sourceOrbit :=
    lt_of_lt_of_le (by decide) (D.sourceOrbit_seven_four_le_globalR h hd σ hσ hmodel)
  exact (min_le_iff.mp (hb.trans hg)).resolve_right (not_le_of_gt hr)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
