module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.SupercriticalNineSource
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.AffineModule
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.SourceCubic
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.NormalClosureCubic.SourceAssembly
public import CFSG.Quasithin.MainForward.SourceReduction
public import Theory.GroupTheory.ReducedNormal.Inheritance

/-!
# Source completion of the centralizer argument in 15.4.8--10

The original normal-centralizer family has cubic quotients by the proved
prime extraction and maximal-prime argument. Its nonempty witness is the
existing source cubic construction. A bad action produces the actual
natural affine-nine quotient. The central Sylow seed has elementary normal
closure in the characteristic-two overgroup; reducedness follows from
inheritance from the Sylow subgroup. Genuine 1.3.7 gives the unique maximal
overgroup, so the earlier 15.4.2(4) contradicts the affine estimate.

The only earlier-source inputs are 15.4.2(1--3), 15.4.2(4), C.2.6 and the
universal 1.3.7. Their discharge stays with the existing Chapter 1,
prime-reduction and centralizer owners. No selected model, reducedness,
centralizer-core identity or uniqueness premise is assumed.

Source: Aschbacher--Smith, printed pp.1156--1160, especially 15.4.9--10.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SourceCompletion
open MaximalPrimeSource MaximalPrimeFive FamilySource CentralizerNormalClosureCubic
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Genuine 1.3.7, universally on the original uppercase star family.
The Chapter 1 owner proves this from 1.3.5; no selected overgroup is an input. -/
@[expose] def Earlier137 : Prop :=
  IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ (T : Sylow 2 G) (Y : Subgroup G),
    Y ∈ Chapter1.XiStar G (T : Subgroup G) →
    IsMaximalTwoLocal (normalizer (Y : Set G)) ∧
      {M : Subgroup G | IsMaximalTwoLocal M ∧ Y ⊔ (T : Subgroup G) ≤ M} =
        {normalizer (Y : Set G)}

omit [Finite G] in
private theorem omega_le (T : Sylow 2 G) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) := by
  intro z hz
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).1

omit [Finite G] in
private theorem sylow_centralizes_omega (T : Sylow 2 G) :
    (T : Subgroup G) ≤ centralizer
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  intro t ht z hz
  exact (((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm

private theorem omega_ne_bot (T : Sylow 2 G) (h : SourceHypotheses T) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≠ ⊥ := by
  let : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot _).mpr
    (MainForward.sylow_ne_bot h.simpleQTKE T)
  have hn := Subgroup.omega_center_ne_bot T.isPGroup'
  intro he
  apply hn
  apply Subgroup.map_injective (f := (T : Subgroup G).subtype)
    (T : Subgroup G).subtype_injective
  simpa only [Stellmacher.omegaOneCenterAmbient, Subgroup.map_bot] using he

private theorem uppercase_noncentral (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) {Y : Subgroup G}
    (hY : Y ∈ Chapter1.Xi G (T : Subgroup G)) :
    ¬ Y ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  intro hc
  exact ((h42 T h).uppercase Y hY).1
    (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))

private theorem centralizer_prime_divisors (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) (h26 : EarlierC26.{u})
    (h44 : Earlier1542Four (G := G)) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card (centralizer
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) → p = 2 ∨ p = 3 := by
  apply PrimeExtraction.centralizer_prime_divisors_of_earlier_source h.simpleQTKE T _
    (omega_le T) (omega_ne_bot T h) (sylow_centralizes_omega T) (h42 T h).solvable
  · intro Y hY
    exact ⟨((h42 T h).uppercase Y hY).1, ((h42 T h).uppercase Y hY).2.2.2⟩
  · intro X hX hm hp
    have hx := source_lemma_15_4_3 T h h42 h26 h44 hX hp hm
    exact ⟨hx.2.2.2.2, hx.2.2.2.1⟩

/-- The genuine 15.4.5 prime restrictions give the cubic quotient of every
member of the original normal-centralizer family. -/
theorem source_cubic_quotient (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) (h26 : EarlierC26.{u})
    (h44 : Earlier1542Four (G := G))
    {X : Subgroup G} (hX : X ∈ NormalCentralizerXi (T : Subgroup G)
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G))) :
    Nat.card (X ⧸ pCore 2 X) = 3 := by
  rw [← index_eq_card]
  rcases centralizer_prime_divisors T h h42 h26 h44 _ hX.1.2.2.2.1
    ((pCore 2 X).index_dvd_card.trans (card_dvd_of_le hX.2.1)) with h2 | h3
  · have ho := hX.1.2.2.2.2
    rw [h2] at ho
    norm_num at ho
  · exact h3

private theorem centralizer_solvable_and_rank (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) :
    Group.IsSolvable (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) ∧
      primeRank 3 (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) ≤ 2 := by
  obtain ⟨M, _, hM, _, hCM, _, _⟩ := h.centralizer_overgroups
  let := (h42 T h).solvable M hM ((sylow_centralizes_omega T).trans hCM)
  refine ⟨Group.isSolvable_of_isSolvable_injective (inclusion_injective hCM), ?_⟩
  exact (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hCM) (inclusion_injective hCM)).trans
    ((h.simpleQTKE.twoLocal_sqtk hM.1).stronglyQuasithin 3 Nat.prime_three (by decide))

/-- Full source 15.4.9 from the genuine earlier implications. The omega
candidate, invariant cubic line and residual lift are constructed internally. -/
theorem source_lemma_15_4_9 (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) (h26 : EarlierC26.{u})
    (h44 : Earlier1542Four (G := G))
    (hne : centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ≠
      (T : Subgroup G)) :
    (NormalCentralizerXi (T : Subgroup G)
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G))).Nonempty := by
  obtain ⟨hs, hr⟩ := centralizer_solvable_and_rank T h h42
  exact SourceCubic.normalCentralizerXi_nonempty_of_earlier_source T _ (omega_le T)
    (sylow_centralizes_omega T) (omega_ne_bot T h) hne hs
    (centralizer_prime_divisors T h h42 h26 h44) hr
    (fun _ hY => uppercase_noncentral T h h42 hY)

private theorem source_closure_reduced (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (he : IsElementaryAbelian 2 (normalClosure
      ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H))) :
    IsPReduced 2 (normalClosure
      ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H)) := by
  let S := T.subtype hTH
  let Z := (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H
  have hZS : Z ≤ (S : Subgroup H) := fun z hz => omega_le T hz
  let E := Z.subgroupOf (S : Subgroup H)
  have hEZ : E ≤ center (S : Subgroup H) := by
    intro z hz
    apply mem_center_iff.mpr
    intro t
    apply Subtype.ext
    apply Subtype.ext
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t t.property
  let : E.Normal := ⟨by
    intro z hz t
    have hc := (mem_center_iff.mp (hEZ hz)) t
    simpa only [hc, mul_inv_cancel_right] using hz⟩
  let := he
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le le_normalClosure
  have hE : IsPReduced 2 E := by
    refine ⟨inferInstance, IsElementaryAbelian.subgroupOf hZS, ?_⟩
    have hC : centralizer (E : Set (S : Subgroup H)) = ⊤ := by
      apply top_unique
      intro t _ z hz
      exact ((mem_center_iff.mp (hEZ hz)) t).symm
    apply bot_unique
    intro x _
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (centralizer (E : Set (S : Subgroup H))) x
    exact (QuotientGroup.eq_one_iff t).mpr (hC.symm ▸ mem_top t)
  have hh := hE.normalClosure_of_sylow_le S (S : Subgroup H) le_rfl E
  rw [map_subgroupOf_eq_of_le hZS] at hh
  exact hh he

omit [Finite G] in
private theorem intrinsic_core_identity (T : Sylow 2 G) (H Z : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (hc : (T : Subgroup G) ⊓ centralizer (sourceClosure H Z : Set G) =
      (H ⊓ centralizer (sourceClosure H Z : Set G)).pCoreIn 2) :
    (T : Subgroup G).subgroupOf H ⊓ centralizer
      (normalClosure (Z.subgroupOf H : Set H) : Set H) =
      (centralizer (normalClosure (Z.subgroupOf H : Set H) : Set H)).pCoreIn 2 := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_inf _ _ _ H.subtype_injective, map_subgroupOf_eq_of_le hTH,
    map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
    map_centralizer_subtype]
  change (T : Subgroup G) ⊓ (H ⊓ centralizer (sourceClosure H Z : Set G)) = _
  rw [← inf_assoc, inf_eq_left.mpr hTH]
  exact hc

/-- Full source 15.4.10. The model, reduced closure, unique overgroup and
literal centralizer-core identity are all produced from the original data. -/
theorem source_lemma_15_4_10 (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) (h26 : EarlierC26.{u})
    (h44 : Earlier1542Four (G := G)) (h137 : Earlier137 (G := G))
    {X M : Subgroup G}
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G)
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)))
    (hM : IsMaximalTwoLocal M) (hXM : X ⊔ (T : Subgroup G) ≤ M) :
    X ≤ M ⊓ centralizer (localV (T : Subgroup G) M : Set G) := by
  refine le_inf (le_sup_left.trans hXM) ?_
  by_contra hcounter
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans hXM
  have hchar : HasCharacteristicTwo M := h.simpleQTKE.evenCharacteristic T M hM hTM
  obtain ⟨_, _, P, hP, _, _, _, hY, _, _, hdata⟩ :=
    SupercriticalNineSource.exists_nine_affine_model T M X hM hTM
      (le_sup_left.trans hXM) hchar hX (source_cubic_quotient T h h42 h26 h44 hX)
      hcounter ((h42 T h).solvable M hM hTM)
      (source_maximal_twoLocal_prime_divisors T h h42 h26 h44 M hM hTM)
      ((h.simpleQTKE.twoLocal_sqtk hM.1).stronglyQuasithin 3 Nat.prime_three (by decide))
      ((h.simpleQTKE.twoLocal_sqtk hM.1).stronglyQuasithin 5 (by decide) (by decide))
      (fun _ hY => uppercase_noncentral T h h42 hY)
      (fun Y hY => ((h42 T h).uppercase Y hY).2.2.1)
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let Y := lift M P
  let H := (Y ⊔ X) ⊔ (T : Subgroup G)
  let W := normalClosure (Z.subgroupOf H : Set H)
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  have hHM : H ≤ M := sup_le (sup_le (lift_le M P) (le_sup_left.trans hXM)) hTM
  have hWH := sourceModule_core_and_elementary T (X := Y ⊔ X) hHM
    (Chapter1.mem_He_iff.mpr hchar)
  have hred : IsPReduced 2 W := source_closure_reduced T H hTH hWH.2.2
  have hZH : Z ≤ H := (omega_le T).trans hTH
  have hH : H ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_, hTH⟩
    intro hb
    apply omega_ne_bot T h
    apply le_bot_iff.mp
    have hzW : Z ≤ W.map H.subtype := by
      intro z hz
      exact ⟨⟨z, hZH hz⟩, le_normalClosure hz, rfl⟩
    exact hzW.trans ((map_mono hred.le_pCore).trans (le_of_eq hb))
  obtain ⟨_, huniq⟩ := h137 h.simpleQTKE T Y (((h42 T h).uppercase Y hY).2.1.2)
  have hnorm (N : Subgroup G) (hN : IsMaximalTwoLocal N) (hYN : Y ⊔ (T : Subgroup G) ≤ N) :
      N = normalizer (Y : Set G) := by
    have hn : N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ Y ⊔ (T : Subgroup G) ≤ N} := ⟨hN, hYN⟩
    rw [huniq] at hn
    exact Set.mem_singleton_iff.mp hn
  have hYM : Y ⊔ (T : Subgroup G) ≤ M := sup_le (lift_le M P) hTM
  have huni : ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N → N = M := by
    intro N hN hHN
    exact (hnorm N hN ((sup_le (le_sup_left.trans le_sup_left) le_sup_right).trans hHN)).trans
      (hnorm M hM hYM).symm
  obtain ⟨_, hc, _, _, _, hm⟩ := hdata
  have hmodel : Nonempty ((H ⧸ centralizer (W : Set H)) ≃* Representation.AffineNine.Special) ∨
      Nonempty ((H ⧸ centralizer (W : Set H)) ≃* Representation.AffineNine.Full) := by
    rcases hm with ⟨f, _, _, _⟩ | ⟨f, _, _, _⟩
    · exact Or.inl ⟨f⟩
    · exact Or.inr ⟨f⟩
  exact affineNine_source_1542_four_contradiction T h h44 H Z M hH hM hHM huni
    hred (intrinsic_core_identity T H Z hTH hc) hWH.1 hmodel

/-- The literal 15.4.8 application. Its cubic, existence and action-control
premises are discharged by the source family above. Only the four genuine
universal earlier implications remain with their original assembly owners. -/
theorem source_lemma_15_4_8 (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) (h26 : EarlierC26.{u})
    (h44 : Earlier1542Four (G := G)) (h137 : Earlier137 (G := G)) :
    centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) = (T : Subgroup G) := by
  obtain ⟨M₁, M₂, hM₁, hM₂, hCM₁, hCM₂, hne⟩ := h.centralizer_overgroups
  have hTM₁ := (sylow_centralizes_omega T).trans hCM₁
  have hTM₂ := (sylow_centralizes_omega T).trans hCM₂
  exact CentralizerNormalClosureCubic.SourceAssembly.centralizer_eq_of_earlier_source
    T _ M₁ M₂ (omega_le T) (sylow_centralizes_omega T) (omega_ne_bot T h) rfl
    hCM₁ hCM₂ hM₁ hM₂ hne
    (h.simpleQTKE.evenCharacteristic T M₁ hM₁ hTM₁)
    (h.simpleQTKE.evenCharacteristic T M₂ hM₂ hTM₂)
    ((h.simpleQTKE.twoLocal_sqtk hM₁.1).stronglyQuasithin 3 Nat.prime_three (by decide))
    ((h.simpleQTKE.twoLocal_sqtk hM₂.1).stronglyQuasithin 3 Nat.prime_three (by decide))
    (source_lemma_15_4_9 T h h42 h26 h44)
    (fun _ hX => source_cubic_quotient T h h42 h26 h44 hX)
    (fun _ hX _ hM hXM => source_lemma_15_4_10 T h h42 h26 h44 h137 hX hM hXM)

/-! Narrow public transports for the solvable pushing-up source companion. -/

omit [Finite G] in
/-- Public source transport used by the solvable pushing-up companion. -/
public theorem source_omega_le (T : Sylow 2 G) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) :=
  omega_le T

omit [Finite G] in
/-- Public source transport used by the solvable pushing-up companion. -/
public theorem source_sylow_centralizes_omega (T : Sylow 2 G) :
    (T : Subgroup G) ≤ centralizer
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
  sylow_centralizes_omega T

/-- Public source transport used by the solvable pushing-up companion. -/
public theorem source_omega_ne_bot (T : Sylow 2 G) (h : SourceHypotheses T) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≠ ⊥ :=
  omega_ne_bot T h

/-- Public source transport used by the solvable pushing-up companion. -/
public theorem source_uppercase_noncentral (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) {Y : Subgroup G}
    (hY : Y ∈ Chapter1.Xi G (T : Subgroup G)) :
    ¬ Y ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
  uppercase_noncentral T h h42 hY

/-- Public source transport used by the solvable pushing-up companion. -/
public theorem source_centralizer_solvable_and_rank (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) :
    Group.IsSolvable (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) ∧
      primeRank 3 (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) ≤ 2 :=
  centralizer_solvable_and_rank T h h42

/-- Public source transport used by the solvable pushing-up companion. -/
public theorem source_normalClosure_reduced (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (he : IsElementaryAbelian 2 (normalClosure
      ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H))) :
    IsPReduced 2 (normalClosure
      ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H)) :=
  source_closure_reduced T H hTH he

omit [Finite G] in
/-- Public source transport used by the solvable pushing-up companion. -/
public theorem source_intrinsic_core_identity (T : Sylow 2 G) (H Z : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (hc : (T : Subgroup G) ⊓ centralizer (sourceClosure H Z : Set G) =
      (H ⊓ centralizer (sourceClosure H Z : Set G)).pCoreIn 2) :
    (T : Subgroup G).subgroupOf H ⊓ centralizer
      (normalClosure (Z.subgroupOf H : Set H) : Set H) =
      (centralizer (normalClosure (Z.subgroupOf H : Set H) : Set H)).pCoreIn 2 :=
  intrinsic_core_identity T H Z hTH hc

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SourceCompletion
