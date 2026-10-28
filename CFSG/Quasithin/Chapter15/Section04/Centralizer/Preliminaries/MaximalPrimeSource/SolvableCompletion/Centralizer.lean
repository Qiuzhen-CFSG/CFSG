module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.SolvableSource
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.SolvableCompletion.PrimeBounds

/-!
# Source 15.4.5 and 15.4.8--10 from solvable pushing up

The solvable C.1.29 source theorem has discharged the former C.2.6 input to
prime reduction. The original cubic witness and affine-nine contradiction
therefore give the centralizer conclusion with only the genuine earlier
15.4.2(1--3) and 15.4.2(4) implications. The universal 1.3.7 consequence is
supplied by the already proved solvable maximal-two-local embedding theorem.
All source groups, normal closures and quotient maps remain literal. The
original completion exposes narrow public transport lemmas for the unchanged
omega, reduced-closure and intrinsic-core arguments.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.C26FreeSource
open MaximalPrimeSource MaximalPrimeFive FamilySource CentralizerNormalClosureCubic
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_lemma_15_4_5 (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G))
    (h44 : Earlier1542Four (G := G)) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card (centralizer
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) → p = 2 ∨ p = 3 := by
  apply PrimeExtraction.centralizer_prime_divisors_of_earlier_source h.simpleQTKE T _
    (SourceCompletion.source_omega_le T) (SourceCompletion.source_omega_ne_bot T h) (SourceCompletion.source_sylow_centralizes_omega T) (h42 T h).solvable
  · intro Y hY
    exact ⟨((h42 T h).uppercase Y hY).1, ((h42 T h).uppercase Y hY).2.2.2⟩
  · intro X hX hm hp
    have hx := MaximalPrimeSource.SolvableCompletion.source_lemma_15_4_3 T h h42 h44 hX hp hm
    exact ⟨hx.2.2.2.2, hx.2.2.2.1⟩

/-- The genuine 15.4.5 prime restrictions give the cubic quotient of every
member of the original normal-centralizer family. -/
theorem source_cubic_quotient (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G))
    (h44 : Earlier1542Four (G := G))
    {X : Subgroup G} (hX : X ∈ NormalCentralizerXi (T : Subgroup G)
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G))) :
    Nat.card (X ⧸ pCore 2 X) = 3 := by
  rw [← index_eq_card]
  rcases source_lemma_15_4_5 T h h42 h44 _ hX.1.2.2.2.1
    ((pCore 2 X).index_dvd_card.trans (card_dvd_of_le hX.2.1)) with h2 | h3
  · have ho := hX.1.2.2.2.2
    rw [h2] at ho
    norm_num at ho
  · exact h3


theorem source_lemma_15_4_9 (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G))
    (h44 : Earlier1542Four (G := G))
    (hne : centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ≠
      (T : Subgroup G)) :
    (NormalCentralizerXi (T : Subgroup G)
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G))).Nonempty := by
  obtain ⟨hs, hr⟩ := SourceCompletion.source_centralizer_solvable_and_rank T h h42
  exact SourceCubic.normalCentralizerXi_nonempty_of_earlier_source T _ (SourceCompletion.source_omega_le T)
    (SourceCompletion.source_sylow_centralizes_omega T) (SourceCompletion.source_omega_ne_bot T h) hne hs
    (source_lemma_15_4_5 T h h42 h44) hr
    (fun _ hY => SourceCompletion.source_uppercase_noncentral T h h42 hY)


theorem source_lemma_15_4_10 (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G))
    (h44 : Earlier1542Four (G := G))
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
      (le_sup_left.trans hXM) hchar hX (source_cubic_quotient T h h42 h44 hX)
      hcounter ((h42 T h).solvable M hM hTM)
      (MaximalPrimeSource.SolvableCompletion.source_maximal_twoLocal_prime_divisors T h h42 h44 M hM hTM)
      ((h.simpleQTKE.twoLocal_sqtk hM.1).stronglyQuasithin 3 Nat.prime_three (by decide))
      ((h.simpleQTKE.twoLocal_sqtk hM.1).stronglyQuasithin 5 (by decide) (by decide))
      (fun _ hY => SourceCompletion.source_uppercase_noncentral T h h42 hY)
      (fun Y hY => ((h42 T h).uppercase Y hY).2.2.1)
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let Y := lift M P
  let H := (Y ⊔ X) ⊔ (T : Subgroup G)
  let W := normalClosure (Z.subgroupOf H : Set H)
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  have hHM : H ≤ M := sup_le (sup_le (lift_le M P) (le_sup_left.trans hXM)) hTM
  have hWH := sourceModule_core_and_elementary T (X := Y ⊔ X) hHM
    (Chapter1.mem_He_iff.mpr hchar)
  have hred : IsPReduced 2 W := SourceCompletion.source_normalClosure_reduced T H hTH hWH.2.2
  have hZH : Z ≤ H := (SourceCompletion.source_omega_le T).trans hTH
  have hH : H ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_, hTH⟩
    intro hb
    apply SourceCompletion.source_omega_ne_bot T h
    apply le_bot_iff.mp
    have hzW : Z ≤ W.map H.subtype := by
      intro z hz
      exact ⟨⟨z, hZH hz⟩, le_normalClosure hz, rfl⟩
    exact hzW.trans ((map_mono hred.le_pCore).trans (le_of_eq hb))
  have h137 := SolvableSource.earlier137_of_source T h h42
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
    hred (SourceCompletion.source_intrinsic_core_identity T H Z hTH hc) hWH.1 hmodel

/-- The literal 15.4.8 application. Its cubic, existence and action-control
premises are discharged by the source family above. Only the genuine
Earlier1542 and Earlier1542Four implications remain with their source owners. -/
theorem source_lemma_15_4_8 (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G))
    (h44 : Earlier1542Four (G := G)) :
    centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) = (T : Subgroup G) := by
  obtain ⟨M₁, M₂, hM₁, hM₂, hCM₁, hCM₂, hne⟩ := h.centralizer_overgroups
  have hTM₁ := (SourceCompletion.source_sylow_centralizes_omega T).trans hCM₁
  have hTM₂ := (SourceCompletion.source_sylow_centralizes_omega T).trans hCM₂
  exact CentralizerNormalClosureCubic.SourceAssembly.centralizer_eq_of_earlier_source
    T _ M₁ M₂ (SourceCompletion.source_omega_le T) (SourceCompletion.source_sylow_centralizes_omega T) (SourceCompletion.source_omega_ne_bot T h) rfl
    hCM₁ hCM₂ hM₁ hM₂ hne
    (h.simpleQTKE.evenCharacteristic T M₁ hM₁ hTM₁)
    (h.simpleQTKE.evenCharacteristic T M₂ hM₂ hTM₂)
    ((h.simpleQTKE.twoLocal_sqtk hM₁.1).stronglyQuasithin 3 Nat.prime_three (by decide))
    ((h.simpleQTKE.twoLocal_sqtk hM₂.1).stronglyQuasithin 3 Nat.prime_three (by decide))
    (source_lemma_15_4_9 T h h42 h44)
    (fun _ hX => source_cubic_quotient T h h42 h44 hX)
    (fun _ hX _ hM hXM => source_lemma_15_4_10 T h h42 h44 hX hM hXM)

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.C26FreeSource
