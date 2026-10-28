module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Tits
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter7.NormalizedSource.Alternatives
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuAssemblyInputs
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF.Parameters
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF.Natural
public import Theory.Representation.BinaryOffender.NormalizerNonFF
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.SmallEven
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.NativeSource
public import Theory.Representation.BinaryPermutation.Faithful
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.G2Recognition
public import Theory.Representation.G2NaturalOffenders
public import Theory.Representation.G2NaturalFaithfulness
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.JankoOneExclusion
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.JankoFourExclusion
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceHeld
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs.JankoFourLyons.Source
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.OddRankOne
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.SourceApplication
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.ActorBounds
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.LargeDegree

/-!
# Partial source selection of the normalized non-Mathieu families

The full Theorems A and C mark the actual central quotient. The linear
three-space branch constructs its prescribed central cover and classifies the
unchanged inflated action. Its natural model gives an offender, so non-FF of
the full component normalizer leaves exactly the half-field tensor, including
Schur degree one. The alternating and binary linear branches are excluded by
their original-action recognizers and offenders; the natural seven-point case
uses an offender in the full symmetric normalizer. The G₂ recognizers transfer
concrete natural-module offenders to the same component normalizer, including
the binary derived endpoint. The Tits source exclusion and the rank-one
quotient markings complete these branches. The odd family reduces further
to PSL₂(25) and PSL₃(3), using the cubic degree bounds and the actual classical
coincidences. The four completed sporadic cubic exclusions leave only M₁₁,
J₂ and Higman–Sims after applying the non-Mathieu premise.

This is a partial sieve, not Proposition 3.2.9: `RemainingModel` records the
other actual quotient families still to be excluded by their cubic source
calculations and the ambient 3.1.8(2)/TI argument. Their assembly stays with
`qt-d-1222-nonmathieu-source-family-sieve`, feeding
`qt-d-1222-nonff-nonmathieu`.

Source: Aschbacher--Smith, Proposition 3.2.9, printed pp.582--583,
Theorem B.4.5, p.87, and Chapter K, pp.451--457.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuFamily
open ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve NonMathieuAssembly
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion

variable {A E : Type*} [Group A] [Finite A] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E] {ρ : Representation (ZMod 2) A E} {Q : Subgroup A}

omit [FiniteDimensional (ZMod 2) E] in
/-- An ambient offender embeds into the full normalizer of the same component. -/
theorem ambient_nonFF (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (hnon : ¬ IsFFModule (normalizerRepresentation (ρ.comp Q.subtype))) :
    ¬ IsFFModule ρ := by
  let : Q.Normal := hs.layer_normal
  intro hff
  apply hnon
  apply isFFModule_linearNormalizer ρ Q
  exact hff.map_equivariant ρ (imageRepresentation ρ) (actionHom ρ)
    (fun _ _ he => hs.faithful (congrArg (fun a : actionImage ρ => a.val.val) he))
    (LinearEquiv.refl _ _) (fun _ _ => rfl)

/-- The actual SL₃ quotient forces its half-field tensor in the non-FF branch. -/
theorem hermitian_of_linear (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (hnon : ¬ IsFFModule (normalizerRepresentation (ρ.comp Q.subtype)))
    {r : ℕ} (hr : 0 < r)
    (hq : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 (2 ^ r)) : HermitianRow hs := by
  have h : SourceHypothesis KnownSimple.IsKnownSimple ρ Q :=
    ⟨inferInstance, inferInstance, hs.sqtk, hs.fitting, hs.quasisimple,
      hs.faithful, hs.irreducible, hs.smallCubic⟩
  obtain ⟨B, _, e, C, _⟩ := SourceFF.exists_binaryField_cover h r hr hq
  let := inflated_irreducible ρ C hs.irreducible
  obtain ⟨hn, hnat | hten⟩ := SourceFF.absolute_models h C e
  · have he := (SourceFF.source_natural_of_absolute h C hnat.1 hnat.2.2).2.1
    apply (ambient_nonFF hs hnon ?_).elim
    apply (isFFModule_iff_quadraticRatio_le_one ρ).mpr
    rw [he]
    norm_num
  · exact ⟨B, C, ⟨e⟩, hn, hten⟩


/-- Express the same tensor witness using a supplied dimension equality.
The action and covering map are unchanged by this numerical transport. -/
theorem hermitian_of_linear_finrank (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (hnon : ¬ IsFFModule (normalizerRepresentation (ρ.comp Q.subtype)))
    {r : ℕ} (hr : 0 < r)
    (hq : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 (2 ^ r))
    (d : ℕ) (hdim : Module.finrank (ZMod 2) E = d) :
    ∃ (B : BinaryField) (C : LinearCover B 3 Q),
      Nonempty ((Q ⧸ center Q) ≃* PSL(3,B.Carrier)) ∧
        letI := inflated_irreducible ρ C hs.irreducible
        let n := schurDegree (inflated ρ C)
        0 < n ∧ B.degree = 2 * n ∧ d = 9 * n ∧
          ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.HasAbsoluteTwistedModel
            (inflated ρ C) n := by
  obtain ⟨B, C, e, hn, hd, he, hm⟩ := hermitian_of_linear hs hnon hr hq
  exact ⟨B, C, e, hn, hd, hdim.symm.trans he, hm⟩

private theorem ff_of_actionCase (hc : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase
    ρ Q (offenderSubgroup ρ)) : IsFFModule ρ := by
  apply (isFFModule_iff_quadraticRatio_le_one ρ).mpr
  cases hc <;> rename_i hq
  all_goals rw [hq]
  case binaryLinear d hd _ _ =>
    rcases hd with rfl | rfl <;> norm_num [ENNReal.div_le_iff]
  all_goals norm_num [ENNReal.div_le_iff]

omit [Finite A] [FiniteDimensional (ZMod 2) E] in
private theorem seven_natural_normalizer_ff
    (a : ActionEquiv (ρ.comp Q.subtype) (alternatingNatural 7)) :
    IsFFModule (normalizerRepresentation (ρ.comp Q.subtype)) := by
  classical
  by_contra hnon
  let b : Representation.Equiv
      ((ρ.comp Q.subtype).comp a.groupEquiv.symm.toMonoidHom)
      ((BinaryPermutation.naturalRepresentation (Fin 7)).comp
        (alternatingGroup (Fin 7)).subtype) := {
    __ := a.linearEquiv
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      have ht := a.intertwines (a.groupEquiv.symm g) v
      simpa only [alternatingNatural, LinearMap.comp_apply, MonoidHom.comp_apply,
        LinearEquiv.coe_coe, MulEquiv.coe_toMonoidHom,
        Subgroup.coe_subtype, MulEquiv.apply_symm_apply] using ht }
  let : ((alternatingGroup (Fin 7)).subtype).range.Normal := by
    rw [Subgroup.range_subtype]
    infer_instance
  have hn := not_isFFModule_of_marked_normal_range
    (BinaryPermutation.naturalRepresentation (Fin 7))
    (BinaryPermutation.naturalRepresentation_injective (Fin 7) (by decide))
    (alternatingGroup (Fin 7)).subtype (ρ.comp Q.subtype)
    a.groupEquiv.symm.toMonoidHom a.groupEquiv.symm.surjective b.symm hnon
  exact hn ⟨_, (ChapterB.Offenders.Odd.isOffender_disjointTranspositions
    (Or.inr rfl) (n := 7) (m := 1) (by decide) (by decide)).2.2.2⟩


/-- Both A₆ and A₇ quotients have an offender in the full component normalizer. -/
theorem alternating_six_seven_excluded (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (hnon : ¬ IsFFModule (normalizerRepresentation (ρ.comp Q.subtype)))
    (hq : Nonempty (Q ⧸ center Q ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (Q ⧸ center Q ≃* alternatingGroup (Fin 7))) : False := by
  have h : ChapterK.Alternating.Input ρ KnownSimple.IsKnownSimple Q :=
    ⟨hs.sqtk, hs.fitting.symm, hs.quasisimple, hs.faithful, hs.irreducible,
      hs.smallCubic, hq⟩
  have hr := ChapterK.Alternating.recognition_of_branches
    (ChapterK.Alternating.sixRecognition_of_inputs ChapterK.Alternating.sixDegree_native_source
      ChapterK.Alternating.RecognitionInputs.Six.fourSpace
      ChapterK.Alternating.RecognitionInputs.Six.normalizer)
    ChapterK.Alternating.sevenRecognition ChapterK.Alternating.tripleSixDegree
    ChapterK.Alternating.tripleSevenExclusion ρ h
  cases ChapterK.Alternating.conclusion_of_recognized ρ h hr with
  | ff _ hc => exact ambient_nonFF hs hnon (ff_of_actionCase hc)
  | sevenNatural _ a _ _ => exact hnon (seven_natural_normalizer_ff a)

/-- The alternating constructor retains only the actual A₅–PSL₂(4) marking. -/
theorem families_of_alternating (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (hnon : ¬ IsFFModule (normalizerRepresentation (ρ.comp Q.subtype)))
    {n : ℕ} (hn : n ≤ 8) (e : Q ⧸ center Q ≃* alternatingGroup (Fin n)) :
    SourceFamilies hs := by
  have hlo := ChapterB.SourceClassification.alternating_degree_ge_five hs e
  have hc : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨2, by decide, GaloisField 2 2, inferInstance, inferInstance,
      GaloisField.card 2 2 (by decide),
      ⟨e.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩⟩
  · exact (alternating_six_seven_excluded hs hnon (Or.inl ⟨e⟩)).elim
  · exact (alternating_six_seven_excluded hs hnon (Or.inr ⟨e⟩)).elim
  · exact (ambient_nonFF hs hnon
      (ff_of_actionCase (ChapterB.SourceClassification.alternating_eight_case hs e))).elim

/-- The two binary linear degrees give FF actions and cannot occur here. -/
theorem binary_linear_excluded (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (hnon : ¬ IsFFModule (normalizerRepresentation (ρ.comp Q.subtype)))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hq : ClassicalGroup.IsPSL (Q ⧸ center Q) n 2) : False :=
  ambient_nonFF hs hnon (ff_of_actionCase
    (ChapterB.SourceClassification.binary_linear_case hs hn hq))

omit [Finite A] in
/-- The Bender constructor marks the three rank-one families on this quotient. -/
theorem families_of_bender (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (hm : ClassificationModels.IsBenderModel (Q ⧸ center Q)) : SourceFamilies hs := by
  cases hm with
  | linear r hr he => exact Or.inl ⟨r, hr, he⟩
  | unitary r hr he => exact Or.inr (Or.inl ⟨r, hr, he⟩)
  | suzuki m hm he => exact Or.inr (Or.inr (Or.inl ⟨m, hm, he⟩))


/-- A natural G₂ offender excludes every ordinary G₂ central quotient. -/
theorem g2_excluded (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (hnon : ¬ IsFFModule (normalizerRepresentation (ρ.comp Q.subtype)))
    {r : ℕ} (hr : 2 ≤ r)
    (hm : ClassificationModels.IsG2At (Q ⧸ center Q) (2 ^ r)) : False := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (show Fintype.card F = 2 ^ r by simpa only [Nat.card_eq_fintype_card] using hcard)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let B : BinaryField := { Carrier := F, degree := r, degree_pos := by omega, card_eq := hcard }
  obtain ⟨M⟩ := ChapterB.SourceClassification.g2_natural_action hs B (by change 1 < r; omega) e
  have hff : IsFFModule (binaryG2 B) :=
    ⟨_, Atlas.G2.NaturalOffenders.natural_elementary_offender hcard (by omega)⟩
  have hinv (g : Atlas.G2.Model F) (v : Atlas.G2.Natural.Space F) :
      M.linearEquiv.symm (binaryG2 B g v) =
        (ρ.comp Q.subtype) (M.groupEquiv.symm g) (M.linearEquiv.symm v) := by
    apply M.linearEquiv.injective
    rw [M.linearEquiv.apply_symm_apply, M.intertwines,
      M.groupEquiv.apply_symm_apply, M.linearEquiv.apply_symm_apply]
  have hqff := hff.map_equivariant (binaryG2 B) (ρ.comp Q.subtype)
    M.groupEquiv.symm.toMonoidHom M.groupEquiv.symm.injective M.linearEquiv.symm hinv
  exact ambient_nonFF hs hnon (hqff.map_equivariant (ρ.comp Q.subtype) ρ
    Q.subtype Subtype.val_injective (LinearEquiv.refl _ _) (fun _ _ => rfl))

/-- At G₂(2)′ the offender in G₂(2) lies in the same full component normalizer. -/
theorem g2_derived_excluded (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (hnon : ¬ IsFFModule (normalizerRepresentation (ρ.comp Q.subtype)))
    (e : Q ⧸ center Q ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  obtain ⟨M⟩ := ChapterB.SourceClassification.g2_binary_natural_action hs e
  let b : Representation.Equiv
      ((ρ.comp Q.subtype).comp M.groupEquiv.symm.toMonoidHom)
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype) := {
    __ := M.linearEquiv
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      have ht := M.intertwines (M.groupEquiv.symm g) v
      simpa only [LinearMap.comp_apply, MonoidHom.comp_apply,
        LinearEquiv.coe_coe, MulEquiv.coe_toMonoidHom,
        Subgroup.coe_subtype, MulEquiv.apply_symm_apply] using ht }
  let : ((commutator (Atlas.G2.Model (ZMod 2))).subtype).range.Normal := by
    rw [Subgroup.range_subtype]
    infer_instance
  have hn := not_isFFModule_of_marked_normal_range (g2Natural (ZMod 2))
    (Atlas.G2.Natural.action_injective (ZMod 2))
    (commutator (Atlas.G2.Model (ZMod 2))).subtype (ρ.comp Q.subtype)
    M.groupEquiv.symm.toMonoidHom M.groupEquiv.symm.surjective b.symm hnon
  exact hn ⟨_, Atlas.G2.NaturalOffenders.natural_elementary_offender
    (F := ZMod 2) (n := 1) (by norm_num) (by decide)⟩

/-- The cubic exclusions and non-Mathieu premise leave exactly these three marked sporadic candidates. -/
theorem sporadic_reduction (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (hnm : ¬ HasMathieuCentralQuotient Q)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (Q ⧸ center Q)) :
    Nonempty ((Q ⧸ center Q) ≃* KnownSimple.SporadicName.m11.Carrier) ∨
    Nonempty ((Q ⧸ center Q) ≃* KnownSimple.SporadicName.j2.Carrier) ∨
    Nonempty ((Q ⧸ center Q) ≃* KnownSimple.SporadicName.hs.Carrier) := by
  rcases hs.fitting with rfl
  have h : ChapterK.SporadicCatalogue.SourceHypotheses ρ :=
    ⟨hs.sqtk, hs.quasisimple, hs.faithful, hs.irreducible, hs.smallCubic⟩
  rcases hm with ⟨name, hne, he⟩ | he
  · cases name with
    | m11 => exact Or.inl he
    | m12 => exact (hnm (Or.inl he)).elim
    | m22 => exact (hnm (Or.inr (Or.inl he))).elim
    | m23 => exact (hnm (Or.inr (Or.inr (Or.inl he)))).elim
    | m24 => exact (hnm (Or.inr (Or.inr (Or.inr he)))).elim
    | j2 => exact Or.inr (Or.inl he)
    | hs => exact Or.inr (Or.inr he)
    | j3 => exact (hne rfl).elim
    | j4 => exact (ChapterK.SporadicCatalogue.sourceExclusion_j4_of_bounded_geometry
        ChapterK.SporadicCatalogue.boundedSourceExclusion_j4 ρ h he).elim
    | he => exact (ChapterK.SporadicCatalogue.sourceExclusion_he ρ h he).elim
    | ru => exact (ChapterK.SporadicCatalogue.sourceExclusion_ru ρ h he).elim
  · exact (ChapterK.SporadicCatalogue.sourceExclusion_j1 ρ h he).elim

/-- The cubic source bound leaves the three classical coincidences and PSL₂(25). -/
theorem odd_linear_two_parameters (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e ≤ 2)
    (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 2 (p ^ e)) :
    p ^ e = 5 ∨ p ^ e = 7 ∨ p ^ e = 9 ∨ p ^ e = 25 := by
  obtain ⟨he', hlo⟩ := ChapterB.SourceClassification.odd_pslTwo_source_bounds hs hp ho he hm
  rcases hs.fitting with rfl
  let h : SourceAction ρ := ⟨hs.sqtk, hs.quasisimple, hs.faithful, hs.irreducible⟩
  have hhi := RankOneSize.source_field_order_le_twentyFive ρ h hp ho he' hlo hm hs.smallCubic
  rcases prime_power_candidates_le_twentyFive hp ho he' hlo hhi with hgood | hbad
  · rcases hgood with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num
  · rcases hbad with hq | hq | hq | hq | hq | hq
    · rw [hq] at hm
      exact ((not_lt_of_ge hs.smallCubic) (RankOneSmall.Eleven.two_lt_cubicRatio ρ h hm)).elim
    · rw [hq] at hm
      exact ((not_lt_of_ge hs.smallCubic)
        (RankOneSmall.source_prime_exclusion ρ h (Or.inl rfl) hm)).elim
    · rw [hq] at hm
      have hd := RankOneSmall.source_seventeen_degree_eq_eight ρ h hm hs.smallCubic
      exact ((not_lt_of_ge hs.smallCubic)
        (RankOneSmall.Seventeen.two_lt_cubicRatio_of_degree_le_eight ρ h hm hd.le)).elim
    · rw [hq] at hm
      exact ((not_lt_of_ge hs.smallCubic)
        (RankOneSmall.source_prime_exclusion ρ h (Or.inr (Or.inl rfl)) hm)).elim
    · rw [hq] at hm
      exact ((not_lt_of_ge hs.smallCubic)
        (RankOneSmall.source_prime_exclusion ρ h (Or.inr (Or.inr rfl)) hm)).elim
    · exact Or.inr (Or.inr (Or.inr hq))

/-- The cubic degree window forces the odd PSL₃ parameter to equal three. -/
theorem odd_linear_three_parameter (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 p) : p = 3 := by
  rcases hs.fitting with rfl
  let h : SourceAction ρ := ⟨hs.sqtk, hs.quasisimple, hs.faithful, hs.irreducible⟩
  have hb := RankThree.source_degree_le_eighteen_pslThree ρ h hp ho hm hs.smallCubic
  by_contra he
  have hp2 := hp.two_le
  have hpne : p ≠ 2 := by intro h; subst p; norm_num at ho
  have hp4 : p ≠ 4 := by intro h; subst p; norm_num at hp
  have hl := RankThree.source_degree_gt_eighteen ρ h hp (by omega) hm
  omega

/-- The odd source catalogue reduces to the surviving families or two literal small linear quotients. -/
theorem families_or_small_odd (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (hnon : ¬ IsFFModule (normalizerRepresentation (ρ.comp Q.subtype)))
    (hm : ChapterA.Section02.IsTheoremCOddModel (Q ⧸ center Q)) :
    SourceFamilies hs ∨ ClassicalGroup.IsPSL (Q ⧸ center Q) 2 25 ∨
      ClassicalGroup.IsPSL (Q ⧸ center Q) 3 3 := by
  cases hm with
  | linear_two p e hp ho he hm =>
    rcases odd_linear_two_parameters hs hp ho he hm with hq | hq | hq | hq
    · rw [hq] at hm
      obtain ⟨e⟩ := ChapterK.OddCharacteristic.altFive_of_psl2_five hm
      exact Or.inl (families_of_alternating hs hnon (by decide) e)
    · rw [hq] at hm
      obtain ⟨e⟩ := ChapterK.OddCharacteristic.psl3Two_of_psl2_seven hm
      have he : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 (2 ^ 1) :=
        ⟨ZMod 2, inferInstance, inferInstance, by norm_num, ⟨e⟩⟩
      exact Or.inl (Or.inr (Or.inr (Or.inr (hermitian_of_linear hs hnon (by decide) he))))
    · rw [hq] at hm
      exact (alternating_six_seven_excluded hs hnon
        (Or.inl (ChapterK.OddCharacteristic.altSix_of_psl2_nine hm))).elim
    · exact Or.inr (Or.inl (hq ▸ hm))
  | linear_three p hp ho hm =>
    exact Or.inr (Or.inr ((odd_linear_three_parameter hs hp ho hm) ▸ hm))
  | unitary_three p hp ho hm =>
    obtain ⟨e⟩ := ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.source_g2Derived_of_cubicRatio_le_two
      ρ Q ⟨hs.sqtk, hs.fitting.symm, hs.quasisimple, hs.faithful, hs.irreducible⟩
      hp ho hm hs.smallCubic
    exact (g2_derived_excluded hs hnon e).elim

/-- Families still requiring their cubic exclusions or the ambient TI argument.
Every constructor retains an actual marking of the central quotient. -/
inductive RemainingModel (Q : Type*) [Group Q] : Prop
  | linear_two_twentyFive (model : ClassicalGroup.IsPSL (Q ⧸ center Q) 2 25)
  | linear_three_three (model : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 3)
  | symplectic (r : ℕ) (hr : 2 ≤ r)
      (model : ClassicalGroup.IsPSp (Q ⧸ center Q) 2 (2 ^ r))
  | triality (r : ℕ) (hr : 1 ≤ r)
      (model : Triality.Standard.IsTrialityGroupAt (2 ^ r) (Q ⧸ center Q))
  | ree (m : ℕ) (hm : 1 ≤ m) (model : Nonempty ((Q ⧸ center Q) ≃* ReeF4.Model m))
  | mathieu_eleven (model : Nonempty ((Q ⧸ center Q) ≃* KnownSimple.SporadicName.m11.Carrier))
  | janko_two (model : Nonempty ((Q ⧸ center Q) ≃* KnownSimple.SporadicName.j2.Carrier))
  | higman_sims (model : Nonempty ((Q ⧸ center Q) ≃* KnownSimple.SporadicName.hs.Carrier))

/-- A partial family sieve, with the unresolved original-action families explicit. -/
theorem families_or_remaining (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (hnm : ¬ HasMathieuCentralQuotient Q)
    (hnon : ¬ IsFFModule (normalizerRepresentation (ρ.comp Q.subtype))) :
    SourceFamilies hs ∨ RemainingModel Q := by
  have hm := ChapterB.SourceClassification.quotient_model_of_theoremsAC
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremC_knownSimple hs
  cases hm with
  | alternating n hn he => exact Or.inl (families_of_alternating hs hnon hn (Classical.choice he))
  | odd hm =>
    rcases families_or_small_odd hs hnon hm with hf | h25 | h3
    · exact Or.inl hf
    · exact Or.inr (.linear_two_twentyFive h25)
    · exact Or.inr (.linear_three_three h3)
  | bender hm => exact Or.inl (families_of_bender hs hm)
  | linear_binary n hn hm => exact (binary_linear_excluded hs hnon hn hm).elim
  | sporadic hm =>
    rcases sporadic_reduction hs hnm hm with h11 | h2 | hhs
    · exact Or.inr (.mathieu_eleven h11)
    · exact Or.inr (.janko_two h2)
    · exact Or.inr (.higman_sims hhs)
  | rank_two r hm =>
    cases hm with
    | linear hr he =>
      exact Or.inl (Or.inr (Or.inr (Or.inr (hermitian_of_linear hs hnon hr he))))
    | symplectic hr he => exact Or.inr (.symplectic r hr he)
    | g2 hr he => exact (g2_excluded hs hnon hr he).elim
    | triality hr he => exact Or.inr (.triality r hr he)
    | ree_f4 m hm _ he => exact Or.inr (.ree m hm he)
    | symplectic_derived _ he =>
      exact (alternating_six_seven_excluded hs hnon (Or.inl ⟨(Classical.choice he).trans
        Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩)).elim
    | g2_derived _ he => exact (g2_derived_excluded hs hnon (Classical.choice he)).elim
    | tits _ he => exact (ChapterB.SourceClassification.tits_exclusion hs (Classical.choice he)).elim

end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuFamily
