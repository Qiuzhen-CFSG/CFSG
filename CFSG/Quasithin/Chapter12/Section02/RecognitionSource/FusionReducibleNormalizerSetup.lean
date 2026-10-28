module

public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalKnownSimple
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore

/-!
# The source setup for Sylow-normalizer control in 12.2.16

The original local-component hypothesis gives the unique maximal two-local
over LT and characteristic two of LT. Thus an escaping Sylow normalizer
forces the two-core of its join with LT to vanish and forbids nontrivial
characteristic subgroups of T normal in LT. The common-normal theorem also
rules out a unique maximal subgroup of LT above T in that counterexample.

For the actual reducible choice, C_V(L) supplies a nonidentity element of
the central omega of T centralizing L. Uniqueness then controls its
centralizer and consequently the centralizer of the whole central omega.
These are the initial source inputs, not a proof of Sylow-normalizer
containment; the block reduction and its terminal analysis remain separate.

Source: Aschbacher–Smith, Theorem 3.3.1(1), Lemmas 3.3.5–6 and 3.3.10(1),
printed pp.586–588; the application in 12.2.16, pp.799–800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open Chapter3
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The genuine maximal two-local and uniqueness premises, with A/C discharged. -/
theorem maximal_unique
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V) :
    IsMaximalTwoLocal (normalizer (L : Set G)) ∧
      ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
        N = normalizer (L : Set G) :=
  h.toHypothesis1221.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))

/-- Characteristic two is inherited on the literal local join. -/
theorem join_characteristicTwo
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    HasCharacteristicTwo (L ⊔ (T : Subgroup G) : Subgroup G) :=
  Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)
    ⟨h.maximal_faithful.1.1.2.2,
      fun _ hx => (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)) hx⟩)

/-- A nontrivial characteristic subgroup of T normal in LT suffices for control. -/
theorem sylow_normalizer_le_of_characteristic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (C : Subgroup (T : Subgroup G)) [C.Characteristic] (hne : C ≠ ⊥)
    (hn : L ⊔ (T : Subgroup G) ≤
      normalizer (C.map (T : Subgroup G).subtype : Set G)) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  apply (normalizer_le_normalizer_characteristic_image (T : Subgroup G) C).trans
  apply normalizer_le_of_unique_maximalTwoLocal (maximal_unique h D).2
    ((T.isPGroup'.to_subgroup C).map (T : Subgroup G).subtype) _ hn
  exact fun he => hne ((C.map_eq_bot_iff_of_injective
    (T : Subgroup G).subtype_injective).mp he)

/-- The source characteristic-subgroup obstruction is intrinsic to T. -/
theorem characteristic_eq_bot_of_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (C : Subgroup (T : Subgroup G)) [C.Characteristic]
    (hn : L ⊔ (T : Subgroup G) ≤
      normalizer (C.map (T : Subgroup G).subtype : Set G)) : C = ⊥ := by
  by_contra hne
  exact hescape (sylow_normalizer_le_of_characteristic h D C hne hn)

/-- Source 3.3.6(b), for any escaping part of the Sylow normalizer. -/
theorem join_core_eq_bot_of_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {A : Subgroup G} (hA : ¬ A ≤ normalizer (L : Set G)) :
    ((L ⊔ (T : Subgroup G)) ⊔ A).pCoreIn 2 = ⊥ := by
  let H := (L ⊔ (T : Subgroup G)) ⊔ A
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans le_sup_left
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  have hn : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  by_contra hne
  exact hA ((le_sup_right.trans hn).trans
    (normalizer_le_of_characteristic_two_unique (join_characteristicTwo h) (maximal_unique h D).2
      (hQT.trans le_sup_right) hne (le_sup_left.trans hn)))

/-- Source 3.3.10(1): a local minimal parabolic has a nontrivial two-core
after adjoining the whole Sylow normalizer. The common-normal input is proved. -/
theorem parabolic_join_core_ne_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {H : Subgroup G} (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hu : Order.HasUniqueMaximalOver (T : Subgroup G) H) :
    (normalizer (T : Set G) ⊔ H).pCoreIn 2 ≠ ⊥ := by
  have hne : (T : Subgroup G) ≠ ⊥ :=
    fun ht => D.ne_bot (bot_unique (D.le_sylow.trans_eq ht))
  have hN : normalizer (T : Set G) ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_, (T : Subgroup G).le_normalizer⟩
    have hc := le_pCoreIn_of_normalizes T.isPGroup' (T : Subgroup G).le_normalizer
      (le_refl (normalizer (T : Set G)))
    exact fun he => hne (bot_unique (hc.trans_eq he))
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      ((pResidual 2 H).map H.subtype ⊔ (T : Subgroup G)) := by
    refine ⟨T.subtype le_sup_right, ?_⟩
    simpa only [Sylow.coe_subtype] using
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤
        (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) from le_sup_right)
  obtain ⟨B, hBT, hBne, hnB⟩ := Chapter3.source_common_normal_knownSimple
    h.simpleQTKE T (normalizer (T : Set G)) H (T : Subgroup G)
    hN hH hu hne le_rfl hs le_rfl
  obtain ⟨hBH, hHB⟩ := normalIn_iff_le_normalizer.mp hnB
  rw [generated_eq_sup] at hBH hHB
  have hc := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hBT) hBH hHB
  exact fun he => hBne (bot_unique (hc.trans_eq he))

/-- The stronger unique-maximal-subgroup premise cannot be assumed in an
escaping configuration: the genuine 3.1.1 theorem would already finish it. -/
theorem not_unique_maximal_of_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ¬ Order.HasUniqueMaximalOver (T : Subgroup G) (L ⊔ (T : Subgroup G)) := by
  intro hu
  have hc := parabolic_join_core_ne_bot h D
    (show L ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (T : Set G) from
      ⟨h.maximal_faithful.1.1.2.2,
        fun _ hx => (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)) hx⟩) hu
  apply hc
  simpa only [sup_comm] using join_core_eq_bot_of_escape h D hescape

/-- Structural 12.2.2 supplies invariance of the actual nonzero fixed subgroup. -/
theorem normalizer_normalizes_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    normalizer (L : Set G) ≤ normalizer (V ⊓ centralizer (L : Set G) : Set G) := by
  have hv := (((structural G T L h).2.2 V D).2.2.2).resolve_right hne
  exact (le_inf hv (normalizer_le_normalizer_centralizer L)).trans
    inf_normalizer_le_normalizer_inf

/-- The reducible choice supplies an actual nontrivial central omega subgroup
centralizing L. This avoids assuming a fixed line or its dimension. -/
theorem fixed_omega_ne_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    (V ⊓ centralizer (L : Set G)) ⊓ omegaCenterIn (T : Subgroup G) ≠ ⊥ :=
  inf_omegaCenterIn_ne_bot_of_normalized_twoGroup _ (T : Subgroup G)
    (inf_le_left.trans D.le_sylow) T.isPGroup'
    (D.sylow_normalizes_component.trans (normalizer_normalizes_fixed h D structural hne)) hne

omit [Finite G] in
/-- The original fixed subgroup witnesses nontriviality of C_T(L). -/
theorem sylow_centralizer_ne_bot (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) ≠ ⊥ := by
  intro he
  exact hne (bot_unique ((inf_le_inf_right _ D.le_sylow).trans_eq he))

/-- Nontrivial C_T(L) controls C_G(Ω₁Z(T)) directly by uniqueness. This is
the centralizer input to the terminal block argument of 3.3.25–31. -/
theorem omega_centralizer_le_of_sylow_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hne : (T : Subgroup G) ⊓ centralizer (L : Set G) ≠ ⊥) :
    centralizer (omegaCenterIn (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  let B := ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ omegaCenterIn (T : Subgroup G)
  have hBne : B ≠ ⊥ :=
    inf_omegaCenterIn_ne_bot_of_normalized_twoGroup _ (T : Subgroup G)
      inf_le_left T.isPGroup'
      ((le_inf (T : Subgroup G).le_normalizer
        (D.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L))).trans
        inf_normalizer_le_normalizer_inf) hne
  have hn : L ⊔ (T : Subgroup G) ≤ centralizer (B : Set G) := by
    apply sup_le
    · exact le_centralizer_iff.mp (show B ≤ centralizer (L : Set G) from
        inf_le_left.trans inf_le_right)
    · apply le_centralizer_iff.mp
      intro b hb
      exact ((mem_omegaCenterIn_iff _ _).mp hb.2).2.1
  exact (centralizer_le (show B ≤ omegaCenterIn (T : Subgroup G) from inf_le_right)).trans
    ((Subgroup.centralizer_le_normalizer _).trans
      (D.normal_subgroup_normalizer_le h.toHypothesis1221
        ((inf_le_left.trans inf_le_left).trans le_sup_right)
        hBne (hn.trans (Subgroup.centralizer_le_normalizer _))))

/-- Actual reducible-module application. No global TI, normalizer containment,
or even no-escape hypothesis is needed for this omega-centralizer bound. -/
theorem omega_centralizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    centralizer (omegaCenterIn (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) :=
  omega_centralizer_le_of_sylow_centralizer h D (sylow_centralizer_ne_bot D hne)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
