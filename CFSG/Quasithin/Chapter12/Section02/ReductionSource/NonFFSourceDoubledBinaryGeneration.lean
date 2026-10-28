module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryGeneration
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryThreeOuter
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Cartan
public import CFSG.Quasithin.ChapterE.GenerationKnownSimple

/-!
# Original binary Cartan action and the remaining odd-normalizer obstruction

The full marked automizer gives n′(Aut_G(W)) = 1 on the actual orbit W.
Every original odd abelian subgroup permuting with T therefore centralizes
W. Applying this to the genuine H-star Hall–Cartan construction shows that
n(H) > 1 forces an odd prime-order subgroup A ≤ C_G(W) whose normalizer
in that same H escapes M.

The original E.3.35 comparison and the proved r ≥ 3 turn w > 1 into just
such an obstruction. Thus the prime-order case of 4.4.3 suffices for w ≤ 1,
and the final conditional consumer supplies w = 1, r = 3 and the actual
rank-five reverse-normalizer hyperplane. This module does not discharge
4.4.3 or claim the binary Baer–Suzuki endgame. No equality of the chosen
seed V with W, and no equality of n(H) with n′, is used.

Source: Aschbacher–Smith 7.3.4,7.5.3,7.6.1, printed pp.699–703,
E.3.35, printed pp.238–239, and 4.4.3, printed p.619,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE
open ChapterE.Section06.FixedPointBounds ChapterE.Section06.FixedPointBounds.ParabolicCartan
open DoubledBinaryGeneration
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual whole-orbit automizer has the table's literal Cartan parameter one. -/
theorem sourceOrbit_binary_nPrime_eq_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) : nPrime (Automizer D.sourceOrbit) = 1 := by
  obtain ⟨_,_,_,_,_,_,a,_⟩ := D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  exact (nPrime_eq_of_mulEquiv a).trans automorphism_nPrime_eq_one

/-- An original odd abelian Sylow permuter centralizes the entire orbit W. -/
theorem sourceOrbit_binary_odd_permuter_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (B : Subgroup G) [IsMulCommutative B]
    (hBM : B ≤ normalizer (L : Set G)) (ho : Odd (Nat.card B))
    (hp : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)) :
    B ≤ centralizer (D.sourceOrbit : Set G) := by
  obtain ⟨_,_,_,_,_,_,a,_⟩ := D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  let W := D.sourceOrbit
  let N := normalizer (W : Set G)
  have hBN : B ≤ N := hBM.trans (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).ge
  have hTN : (T : Subgroup G) ≤ N := D.sourceOrbit_weakClosure_setup.normalizes
  let q : N →* MulAut Matrix.PSL3Two.SL :=
    a.toMonoidHom.comp W.normalizerMonoidHom.rangeRestrict
  have hqs : Function.Surjective q := a.surjective.comp
    W.normalizerMonoidHom.rangeRestrict_surjective
  have hperm : (B.subgroupOf N : Set N) * (T.subtype hTN : Set N) =
      (T.subtype hTN : Set N) * (B.subgroupOf N : Set N) := by
    apply Set.image_injective.mpr N.subtype_injective
    rw [Set.image_mul,Set.image_mul]
    change ((B.subgroupOf N).map N.subtype : Set G) *
        (((T : Subgroup G).subgroupOf N).map N.subtype : Set G) =
      (((T : Subgroup G).subgroupOf N).map N.subtype : Set G) *
        ((B.subgroupOf N).map N.subtype : Set G)
    rwa [map_subgroupOf_eq_of_le hBN,map_subgroupOf_eq_of_le hTN]
  have hodd : Odd (Nat.card (B.subgroupOf N)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv]
  have hk := odd_permuter_le_kernel q hqs (T.subtype hTN) (B.subgroupOf N) hodd hperm
  intro b hb
  have he := hk (show (⟨b,hBN hb⟩ : N) ∈ B.subgroupOf N from hb)
  have hact : W.normalizerMonoidHom ⟨b,hBN hb⟩ = 1 := by
    have hh : W.normalizerMonoidHom.rangeRestrict ⟨b,hBN hb⟩ = 1 :=
      a.injective (he.trans (map_one a.toMonoidHom).symm)
    exact congrArg Subtype.val hh
  change (⟨b,hBN hb⟩ : N) ∈ W.normalizerMonoidHom.ker at hact
  rw [normalizerMonoidHom_ker] at hact
  exact hact

/-- E.3.35 on the actual marked doubled orbit, retaining its original H-star carrier. -/
theorem sourceOrbit_doubled_min_parameters_le_generation
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    min (globalW D.sourceOrbit T) (globalR D.sourceOrbit) ≤ (generationParameter H : ℕ∞) := by
  have h61 := D.sourceOrbit_hypothesisE61_of_markedDoubled h hd
  have hu : maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) : Subgroup G) : Set G)) =
      {normalizer (L : Set G)} := by
    ext N
    constructor
    · intro hN
      exact Set.mem_singleton_iff.mpr (h61.unique N hN.1 (inf_le_right.trans hN.2))
    · intro hN
      obtain rfl := Set.mem_singleton_iff.mp hN
      exact ⟨h61.maximalTwoLocal,h61.normalizer_sylowCentralizer_le⟩
  by_contra hn
  apply hH.1.2
  apply SourceContainment.le_of_sqtk_knownSimple D.sourceOrbit_weakClosure_setup
    (T.subtype hH.1.1.2) (Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1)
    hu (inf_le_right.trans h61.centralizer_le) ?_ (lt_of_not_ge hn)
  change (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) ≤
    ((T : Subgroup G).subgroupOf H).map H.subtype
  rw [map_subgroupOf_eq_of_le hH.1.1.2]
  exact inf_le_left

/-- Large generation forces an actual odd prime-order subgroup centralizing W
whose normalizer in the same H escapes M. This isolates the exact remaining
4.4.3 input without assuming Hall faithfulness or replacing W by its seed. -/
theorem sourceOrbit_binary_hstar_odd_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ A : Subgroup G,
      A ≤ H ∧ A ≤ centralizer (D.sourceOrbit : Set G) ∧ Nat.card A = p ∧
      ¬ H ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  let S := D.fundamentalSetup h.toHypothesis1221
  have hSM : S.maximalLocal = normalizer (L : Set G) := by
    change normalizer (Chapter3.Section02.localOrbit T L : Set G) = _
    rw [D.localOrbit_eq]
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) S.maximalLocal := hSM.symm ▸ hH
  obtain ⟨hP,f,_,hf,d,he,hperm,hescape⟩ :=
    Chapter10.source_hstar_cartan_data_of_generation_gt_one S hH' hlarge
  let := d.witness.abelian
  have hBM : d.witness.abelianGroup.map H.subtype ≤ normalizer (L : Set G) := by
    apply map_le_iff_le_comap.mpr
    change d.witness.abelianGroup ≤ (normalizer (L : Set G)).subgroupOf H
    simpa only [hSM] using d.hall_le.trans_eq he
  have ho : Odd (Nat.card (d.witness.abelianGroup.map H.subtype)) :=
    d.witness.odd.of_dvd_nat (card_map_dvd _ _)
  have hC := D.sourceOrbit_binary_odd_permuter_centralizes h hd F hF hmodel
    (d.witness.abelianGroup.map H.subtype) hBM ho hperm
  have hne : Nat.card d.witness.cyclicGroup ≠ 1 := by
    rw [d.witness.card]
    have hh : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega)
    omega
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd hne
  let : Fact p.Prime := ⟨hp⟩
  have hoddC : Odd (Nat.card d.witness.cyclicGroup) :=
    d.witness.odd.of_dvd_nat (card_dvd_of_le d.witness.cyclic_le)
  have hpo : Odd p := hoddC.of_dvd_nat hpd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' p hpd
  let A₀ : Subgroup H := zpowers (x : H)
  have hA₀ : A₀ ≤ d.witness.cyclicGroup := zpowers_le.mpr x.property
  have hc : Nat.card A₀ = p := by simpa only [A₀,Nat.card_zpowers,orderOf_submonoid] using hx
  let A := A₀.map H.subtype
  have hA : Nat.card A = p := (card_map_of_injective H.subtype_injective).trans hc
  refine ⟨p,hp,hpo,A,map_subtype_le _,(map_mono (hA₀.trans d.witness.cyclic_le)).trans hC,hA,?_⟩
  simpa only [hSM] using hescape p inferInstance A₀ hpo hA₀ (IsPGroup.of_card (n := 1) (by simpa using hc))

/-- Failure of w≤1 on the original orbit produces the actual odd-normalizer
obstruction. No independent source premise is added to this reduction. -/
theorem sourceOrbit_binary_globalW_or_odd_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    globalW D.sourceOrbit T ≤ 1 ∨
      ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        1 < generationParameter H ∧ ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ A : Subgroup G,
          A ≤ H ∧ A ≤ centralizer (D.sourceOrbit : Set G) ∧ Nat.card A = p ∧
          ¬ H ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  by_cases hw : globalW D.sourceOrbit T ≤ 1
  · exact Or.inl hw
  have h61 := D.sourceOrbit_hypothesisE61_of_markedDoubled h hd
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (Chapter3.hasMaximalOutside_of_many T hmany _ h61.maximalTwoLocal h61.sylow_le)
  have hr := D.sourceOrbit_binary_three_le_globalR h hd hnon F hF hmodel
  have hbound := D.sourceOrbit_doubled_min_parameters_le_generation h hd hH
  have hbig : (1 : ℕ∞) < (generationParameter H : ℕ∞) :=
    (lt_min (lt_of_not_ge hw) (lt_of_lt_of_le (by decide) hr)).trans_le hbound
  have hn : 1 < generationParameter H := by exact_mod_cast hbig
  exact Or.inr ⟨H,hH,hn,D.sourceOrbit_binary_hstar_odd_escape h hd F hF hmodel hH hn⟩

/-- The prime-order part of original 4.4.3 suffices for w≤1; the marked
Cartan calculation and actual generation comparison are discharged above. -/
theorem sourceOrbit_binary_globalW_le_one_of_odd_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (hcontrol : ∀ (p : ℕ), p.Prime → Odd p → ∀ A : Subgroup G,
      A ≤ centralizer (D.sourceOrbit : Set G) → Nat.card A = p →
      normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    globalW D.sourceOrbit T ≤ 1 := by
  rcases D.sourceOrbit_binary_globalW_or_odd_escape h hd hmany hnon F hF hmodel with hw | he
  · exact hw
  · obtain ⟨H,_,_,p,hp,ho,A,_,hAC,hcard,hn⟩ := he
    exact (hn (inf_le_right.trans (hcontrol p hp ho A hAC hcard))).elim

/-- The original FWCI equality and reverse-normalizer hyperplane follow once
the remaining odd-normalizer input is proved. No r or w bound is assumed. -/
theorem sourceOrbit_binary_offender_of_odd_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (hcontrol : ∀ (p : ℕ), p.Prime → Odd p → ∀ A : Subgroup G,
      A ≤ centralizer (D.sourceOrbit : Set G) → Nat.card A = p →
      normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    globalW D.sourceOrbit T = 1 ∧ globalR D.sourceOrbit = 3 ∧
      ∃ g : G,
        ⁅D.sourceOrbit,D.sourceOrbit.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
        inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g) ≤
          inducedAutomizer D.sourceOrbit L ∧
        Nat.card (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) :
          Subgroup G) = 8 ∧
        offenderFixedSpan D.sourceOrbit g = D.sourceOrbit ⊓
          normalizer (D.sourceOrbit.map (MulAut.conj g).toMonoidHom : Set G) ∧
        (offenderFixedSpan D.sourceOrbit g).relIndex D.sourceOrbit = 2 ∧
        rank (offenderFixedSpan D.sourceOrbit g) = 5 := by
  have hw := D.sourceOrbit_binary_globalW_le_one_of_odd_control h hd hmany hnon F hF hmodel hcontrol
  have hr := D.sourceOrbit_binary_three_le_globalR h hd hnon F hF hmodel
  have he := D.sourceOrbit_binary_forced_parameters h hd F hF hmodel hnon hw hr
  exact ⟨he.1,he.2.1,D.sourceOrbit_binary_exists_offender_geometry h hd F hF hmodel hnon hw hr⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
