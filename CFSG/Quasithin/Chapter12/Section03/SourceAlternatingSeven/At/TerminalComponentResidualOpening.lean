module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentResidualOpening
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentPreparation

/-!
# TerminalComponentResidualOpening at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalComponentResidualOpening`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 Section02.RecognitionSource Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

theorem sylow_normalizer_le_original_at (S : Setup T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  let := S.chosen.elementary
  exact (ChapterE.normalizer_le_weakClosure_normalizer V (T : Subgroup G) 0).trans
    (ChapterE.SourceContainment.normalizer_weakClosure_zero_le
      ⟨S.chosen.ne_bot, S.chosen.le_sylow, ((structural L S.hypothesis).2.2 V S.chosen).1⟩
      (lt_trans (by decide) hw) (chosen_centralizer_unique_at S structural))

theorem minimalParabolic_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    ChapterB.IsMinimalParabolicOver (T.subtype P.minimal.1.1.2) ⊤ := by
  have hp := Chapter3.HStar.minimalParabolic T S.chosen.sylow_normalizes_component P.minimal
    (Or.inl (sylow_normalizer_le_original_at S structural hw))
  obtain ⟨hTB,hBH,_⟩ := Chapter3.HStar.unique_maximal T
    S.chosen.sylow_normalizes_component P.minimal
  exact (ChapterB.intrinsic_minimalParabolic T P.H
    (P.H ⊓ normalizer (L : Set G)) hp hTB hBH).1

theorem exists_generating_component_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    ∃ X : Subgroup G, HStarGeneratingComponent T L P.H X := by
  let U := T.subtype P.minimal.1.1.2
  obtain ⟨X,hX,hq,hgen,_⟩ := ChapterE.Structure.source_original_component
    (Chapter3.sqtk_of_mem_H S.hypothesis.simpleQTKE P.minimal.1.1.1) U
    (P.minimalParabolic_at structural hw) (P.not_solvable_at structural hr hw)
  let X' := X.map P.H.subtype
  have hX'H : X' ≤ P.H := map_subtype_le _
  have hXsub : X'.subgroupOf P.H = X := comap_map_eq_self_of_injective P.H.subtype_injective _
  have hgen' : X' ⊔ (T : Subgroup G) = P.H := by
    have he := congrArg (map P.H.subtype) hgen
    have ht : ((U : Subgroup P.H)).map P.H.subtype = (T : Subgroup G) :=
      map_subgroupOf_eq_of_le P.minimal.1.1.2
    simpa only [Subgroup.map_sup, ht, ← MonoidHom.range_eq_map, range_subtype] using he
  let e : X ≃* X' := X.equivMapOfInjective P.H.subtype P.H.subtype_injective
  let eq : (X ⧸ pCore 2 X) ≃* (X' ⧸ pCore 2 X') :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let := hq
  have hq' : IsQuasisimple (X' ⧸ pCore 2 X') := IsQuasisimple.of_mulEquiv eq
  let := hX.perfect
  let : Group.IsNilpotent (P.H ⧸ pResidual 2 P.H) := (isPGroup_quotient_pResidual 2).isNilpotent
  have hXK : X ≤ pResidual 2 P.H := le_of_isPerfect_of_solvable_quotient X (pResidual 2 P.H)
  have hres : P.K = componentOrbit X' (T : Subgroup G) := by
    rw [K, embedded_pResidual_eq_conjugateSpanBy X' (T : Subgroup G) P.H
      (map_mono hXK) T.isPGroup' hgen', conjugateSpanBy_eq_iSup_conj]
    rfl
  have hout : ¬ X' ≤ normalizer (L : Set G) := by
    intro hx
    apply P.minimal.1.2
    rw [← hgen']
    exact sup_le hx S.chosen.sylow_normalizes_component
  refine ⟨X', ⟨⟨hX'H,hXsub.symm ▸ hX⟩,hq',hgen',hres,hout,?_⟩⟩
  intro he
  apply hout
  exact ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)).trans
    (centralizer_le (le_conjugateSpanBy _ _))).trans
      (omega_center_centralizer_le_at S D structural)

private theorem omega_le_join_reduced_at {Y : Subgroup G}
    (hY : Y ∈ Chapter1.L G (T : Subgroup G)) :
    P.Z ≤ (reducedTwoSubgroup (Y ⊔ (T : Subgroup G) : Subgroup G)).map
      (Y ⊔ (T : Subgroup G)).subtype := by
  let J := Y ⊔ (T : Subgroup G)
  let U : Sylow 2 J := T.subtype le_sup_right
  have hc := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (S.hypothesis.simpleQTKE.evenCharacteristic T)
      ⟨hY.2.2, show (T : Subgroup G) ≤ J from le_sup_right⟩)
  have hh := map_mono (f := J.subtype) (sylow_omegaCenter_le_reduced U hc)
  change (Stellmacher.omegaOneCenterAmbient (U : Subgroup J)).map J.subtype ≤ _ at hh
  rw [← Stellmacher.omegaOneCenterAmbient_map_injective J.subtype J.subtype_injective] at hh
  change Stellmacher.omegaOneCenterAmbient (((T : Subgroup G).subgroupOf J).map J.subtype) ≤ _ at hh
  rwa [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)] at hh

private theorem fitting_map_le_at {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  rintro N ⟨hN, hnil⟩
  apply map_le_iff_le_comap.mp
  let := hnil
  exact le_sSup ⟨hN.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩

private theorem common_odd_prime_at {A : Type*} [Group A] [Finite A]
    (h : A36Common A) (hn : ¬ IsQuasisimple A) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card (fittingSubgroup A) := by
  have hne : Nat.card (fittingSubgroup A) ≠ 1 := by
    intro he
    have hb : fittingSubgroup A = ⊥ := (card_le_one_iff_eq_bot _).mp he.le
    let := h.2.1
    exact hn (IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot))
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd hne
  refine ⟨p, hp, ?_, hd⟩
  rcases hp.eq_two_or_odd' with rfl | ho
  · have hc := pPrimeCore_coprime_card (p := 2) (G := A)
    rw [← h.1] at hc
    have hh := Nat.dvd_gcd (dvd_refl 2) hd
    rw [hc] at hh
    norm_num at hh
  · exact ho

private theorem fitting_prime_transport_at {A B : Type*} [Group A] [Group B] [Finite B]
    (e : A ≃* B) {p : ℕ} (hd : p ∣ Nat.card (fittingSubgroup A)) :
    p ∣ Nat.card (fittingSubgroup B) := by
  rw [Nat.card_congr (e.subgroupMap (fittingSubgroup A)).toEquiv] at hd
  exact hd.trans (card_dvd_of_le (fitting_map_le_at e))

private theorem exists_odd_radical_prime_at
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h36 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ →
      ∀ C : Subgroup A, C.IsCComponent → A36Conclusion C)
    {Y : Subgroup G} (hY : Y ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (Y ⧸ pCore 2 Y)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card (fittingSubgroup (XiQuotient Y)) := by
  have hQ := uniqueness_local_quotient_sqtk hG hY.2.2
  let e := radicalLocalQuotientEquiv hY
  have hc := proposition_1_2_1_four_earlier_conclusion h36 hQ hY.1
  have hn' : ¬ IsQuasisimple (radicalLocalImage T Y) := by
    intro h
    let := h
    exact hn (IsQuasisimple.of_mulEquiv e.symm)
  obtain ⟨p,hp,ho,hd⟩ := common_odd_prime_at hc.2 hn'
  exact ⟨p,hp,ho,fitting_prime_transport_at e.symm hd⟩

include P in

theorem nonquasisimple_overgroup_le_original_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {Y : Subgroup G} (hY : FaithfulMaximalLocal T Y)
    (hn : ¬ IsQuasisimple (Y ⧸ pCore 2 Y)) :
    Y ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  obtain ⟨p,hp,ho,hd⟩ := exists_odd_radical_prime_at S.hypothesis.simpleQTKE h36 hY.1.1 hn
  let : Fact p.Prime := ⟨hp⟩
  have hstar := Chapter3.RadicalCentralization.ChosenStars.XiP_mem_XiStar
    S.hypothesis.simpleQTKE T hY.1 hn ho hd
  have hrad := Chapter3.RadicalCentralization.ChosenStars.maximal_solvableRadical_centralizes_sylowJoin
    S.hypothesis.simpleQTKE T P.many_maximal_overgroups_at hY.1 hn
  have hXiZ : XiP p Y ≤ centralizer (P.Z : Set G) :=
    ((Chapter3.RadicalCentralization.XiP_le_solvableRadical Y p).trans hrad).trans
      (centralizer_le (P.omega_le_join_reduced_at hY.1.1))
  have hXiM : XiP p Y ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le (hXiZ.trans (omega_center_centralizer_le_at S D structural))
      S.chosen.sylow_normalizes_component
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
    S.hypothesis.simpleQTKE T S.hypothesis.maximal_faithful.1
  have hmax : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [S.chosen.localOrbit_eq] using hu.normalizer_maximal
  have he : normalizer (L : Set G) = normalizer (XiP p Y : Set G) := by
    have hh : normalizer (L : Set G) ∈
        {M : Subgroup G | IsMaximalTwoLocal M ∧ XiP p Y ⊔ (T : Subgroup G) ≤ M} :=
      ⟨hmax,hXiM⟩
    rw [(Chapter1.XiEmbedding.normalizer_unique_of_XiStar_knownSimple
      S.hypothesis.simpleQTKE T hstar).2] at hh
    exact Set.mem_singleton_iff.mp hh
  rw [he]
  exact sup_le (Y.le_normalizer.trans (normalizer_le_normalizer_XiP p Y)) hstar.1.invariant

theorem generating_component_overgroup_hypothesis_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {X Y : Subgroup G} (C : HStarGeneratingComponent T L P.H X)
    (hXY : X ≤ Y) (hY : Y ∈ Chapter1.LStar G (T : Subgroup G)) :
    Hypothesis1223 KnownSimple.IsKnownSimple T Y := by
  have hf := Chapter1.Section02.Adequate.faithful_local_overgroup T
    (S.hypothesis.simpleQTKE.evenCharacteristic T) (C.faithful_at S.hypothesis P.minimal) hY.1 hXY
  have hfaithful : FaithfulMaximalLocal T Y :=
    ⟨hY,((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T Y).mp hf).2⟩
  have hq : IsQuasisimple (Y ⧸ pCore 2 Y) := by
    by_contra hn
    exact C.escapes (hXY.trans (le_sup_left.trans
      (P.nonquasisimple_overgroup_le_original_at structural hfaithful hn)))
  exact { S.hypothesis with maximal_faithful := hfaithful, quasisimple := hq }

theorem generating_component_eq_residual_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    {X : Subgroup G} (C : HStarGeneratingComponent T L P.H X) : X = P.K := by
  obtain ⟨Y,hY,hXY⟩ := (C.exists_maximal_overcomponent P.minimal).2
  have hYhyp := P.generating_component_overgroup_hypothesis_at structural C hXY hY
  obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural Y hYhyp).2.1
  apply C.eq_residual_of_normalized
  exact Chapter1.Section02.MovedMaximality.local_chain_normalizes_of_sylow_overgroup_unique T
    (C.exists_maximal_overcomponent P.minimal).1 hY.1 hXY (structural Y hYhyp).1
    (E.sylowOvergroupComponentUnique_of_alternatives hYhyp.quasisimple (modules Y W hYhyp E))

theorem residual_generating_component_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    HStarGeneratingComponent T L P.H P.K := by
  obtain ⟨X,C⟩ := P.exists_generating_component_at structural hr hw
  exact P.generating_component_eq_residual_at structural modules C ▸ C

theorem residual_local_and_quasisimple_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    P.K ∈ Chapter1.L G (T : Subgroup G) ∧ IsQuasisimple (P.K ⧸ pCore 2 P.K) := by
  have C := P.residual_generating_component_at structural modules hr hw
  exact ⟨(C.exists_maximal_overcomponent P.minimal).1,C.quasisimple⟩

theorem residual_overgroup_hypothesis_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    {Y : Subgroup G} (hY : Y ∈ Chapter1.LStar G (T : Subgroup G)) (hKY : P.K ≤ Y) :
    Hypothesis1223 KnownSimple.IsKnownSimple T Y :=
  P.generating_component_overgroup_hypothesis_at structural
    (P.residual_generating_component_at structural modules hr hw) hKY hY

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

