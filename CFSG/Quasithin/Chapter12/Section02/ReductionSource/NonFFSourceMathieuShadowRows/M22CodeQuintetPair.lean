module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodePair
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeDegree
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceWitnessSaturation
public import CFSG.Quasithin.Chapter8.Section02.Offenders.FixedPoints
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeQuintet

/-!
# The original M22-code pair and its quintet fixed space

The native cubic calculation excludes degree two, so the original pair has
degree one. Positive weak closure makes its core actor a 1-offender. The
existing non-FF fixed-space argument and r ≥ 6 force r = 6, actor rank five,
and fixed rank four. The fixed subgroup equals both the original conjugate
intersection and the full actor centralizer kernel; the same pair centralizes it.
The intrinsic rank-five catalogue identifies the actor with the quintet core
and proves that the original Sylow normalizes its fixed four-space.

All pairs lie in the supplied original H-star. The full covering quotient,
original component and full automizer marking are retained. These are
the M22-code assertions of 8.2.3 and the table/fixed-subgroup assertions of
8.2.5; the subsequent normalizer argument and M22 exclusion are not asserted.
Source: Aschbacher--Smith 8.2.2--5,H.14.3,H.16.7, printed pp.714--717,397,405,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual original M22-code pair has degree one, with no extra local premise. -/
theorem sourceOrbit_m22_code_pair_degree_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      GeometricSelected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S := by
  obtain ⟨I,k,i,S,s,_⟩ := D.sourceOrbit_m22_code_geometric_pair h hmany hV hnon d hH
  obtain ⟨a,hinj,hE,_⟩ := D.sourceOrbit_m22_code_full_automizer h.toHypothesis1221 d
  have hr : primeRank 2 (Automizer D.sourceOrbit) ≤ 5 :=
    (Theory.GroupTheory.primeRank_le_of_injective 2
      (m22PairStabilizerEquivAut.toMonoidHom.comp a)
      (m22PairStabilizerEquivAut.injective.comp hinj)).trans m22_automorphism_twoRank_le_five
  have hk := s.m22_code_parameter_one hr a hinj
    (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv) hE
  exact ⟨I,i,S,hk ▸ s⟩

/-- The original code offender has w = 1, r = 6, actor rank five and fixed rank four. -/
theorem sourceOrbit_m22_code_fixed_pair
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      let A := offenderNormalizer D.sourceOrbit i.val⁻¹
      let U := D.sourceOrbit ⊓ centralizer (A : Set G)
      let B := inducedAutomizer D.sourceOrbit A
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      globalW D.sourceOrbit (T : Subgroup G) = 1 ∧
      globalR D.sourceOrbit = 6 ∧
      IsWOffenderAt D.sourceOrbit T i.val⁻¹ ∧
      A = D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ∧
      A ≤ T ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = A ⊓ centralizer (D.sourceOrbit : Set G) ∧
      I ≤ centralizer (U : Set G) ∧
      rank B = 5 ∧ rank U = 4 ∧
      ⁅⁅⁅D.sourceOrbit,A⁆,A⁆,A⁆ = ⊥ := by
  obtain ⟨I,i,S,s⟩ := D.sourceOrbit_m22_code_pair_degree_one h hmany hV hnon d hH
  obtain ⟨a,hinj,hE,_⟩ := D.sourceOrbit_m22_code_full_automizer h.toHypothesis1221 d
  have hrank : primeRank 2 (Automizer D.sourceOrbit) ≤ 5 :=
    (Theory.GroupTheory.primeRank_le_of_injective 2
      (m22PairStabilizerEquivAut.toMonoidHom.comp a)
      (m22PairStabilizerEquivAut.injective.comp hinj)).trans m22_automorphism_twoRank_le_five
  have hpos := D.sourceOrbit_m22_code_globalW_pos h hmany hV hnon d
  obtain ⟨hw,hOff,hA,hAT,hker⟩ := s.offender_of_parameter_bound
    D.sourceOrbit_weakClosure_setup (Order.one_le_iff_pos.mpr hpos)
  have hFF := D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon
  have hr := D.sourceOrbit_m22_code_globalR_ge_six h hmany hV hnon d
  obtain ⟨hr6,hfive,_,hfour,hf⟩ := code_row_parameters D.sourceOrbit T i.val⁻¹
    D.sourceOrbit_weakClosure_setup hFF hOff hw 5 (by decide) hr hrank hker
  have hv : rank D.sourceOrbit = 10 :=
    (Chapter7.log_card_eq_finrank D.sourceOrbit).trans
      ((D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv).finrank_eq.trans finrank_m22Code)
  rw [hv] at hfour
  have hcentral := generated_pair_centralizes_fixed D.sourceOrbit i.val⁻¹ hf
  rw [s.generate] at hcentral
  have hc := selected_actor_cubic I (normalizer (L : Set G)) D.sourceOrbit
    (s.generate ▸ le_sup_left) S i s.twoConjugate
  rw [←hA] at hc
  exact ⟨I,i,S,s.toSelected (one_dvd _),hw,hr6,hOff,hA,hAT,hf,hf.trans hker.symm,
    hcentral,hfive,hfour,hc⟩

/-- The same pair has the literal quintet marking and its fixed subgroup is normal in T. -/
theorem sourceOrbit_m22_code_quintet_pair
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      let A := offenderNormalizer D.sourceOrbit i.val⁻¹
      let U := D.sourceOrbit ⊓ centralizer (A : Set G)
      let B := inducedAutomizer D.sourceOrbit A
      let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      globalW D.sourceOrbit (T : Subgroup G) = 1 ∧ globalR D.sourceOrbit = 6 ∧
      IsWOffenderAt D.sourceOrbit T i.val⁻¹ ∧
      A = D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ∧
      A ≤ T ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = A ⊓ centralizer (D.sourceOrbit : Set G) ∧ I ≤ centralizer (U : Set G) ∧
      rank B = 5 ∧ rank U = 4 ∧ (U.subgroupOf T).Normal ∧
      (T : Subgroup G) ≤ normalizer (U : Set G) ∧ ⁅⁅⁅D.sourceOrbit,A⁆,A⁆,A⁆ = ⊥ ∧
      ∃ a : Automizer D.sourceOrbit →* MathieuCode.m22PairStabilizer, Function.Injective a ∧
        (∀ b v, E (automizerRepresentation D.sourceOrbit b v) = m22OuterCodeRepresentation (a b) (E v)) ∧
        ∃ c : MathieuCode.m22PairStabilizer,
          (B.map a).map (MulAut.conj c).toMonoidHom = m22OuterQuintetKernel m22SourceSextet := by
  obtain ⟨I,i,S,s,hw,hr,hOff,hA,hAT,hfix,hker,hcentral,hfive,hfour,hc⟩ :=
    D.sourceOrbit_m22_code_fixed_pair h hmany hV hnon d hH
  obtain ⟨a,hinj,hE,_⟩ := D.sourceOrbit_m22_code_full_automizer h.toHypothesis1221 d
  let B := inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit i.val⁻¹)
  let : IsElementaryAbelian 2 B := offender_inducedAutomizer_elementary D.sourceOrbit i.val⁻¹
  let : IsElementaryAbelian 2 (B.map a) := IsElementaryAbelian.map _
  have hm : rank (B.map a) = 5 := (rank_map_injective a hinj B).trans hfive
  have hmark := NormalizedShadowRows.M22CodeQuintet.quintet_marking (B.map a) hm
  let P := inducedAutomizer D.sourceOrbit (T : Subgroup G)
  have hp : IsPGroup 2 P := T.2.comap_subtype.map _
  have hBP : B ≤ P := map_mono (comap_mono hAT)
  have hn := NormalizedShadowRows.M22CodeQuintet.normalized_in_two_group
    (B.map a) (P.map a) (hp.map a) (map_mono hBP) hm
  have hnormalize : P ≤ normalizer (B : Set (Automizer D.sourceOrbit)) := by
    intro b hb
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply Subgroup.map_injective (f := a) hinj
    change (B.map (MulAut.conj b).toMonoidHom).map a = B.map a
    rw [map_map]
    have heq : a.comp (MulAut.conj b).toMonoidHom =
        (MulAut.conj (a b)).toMonoidHom.comp a := by
      ext x
      simp [MulAut.conj_apply]
    rw [heq,←map_map]
    exact mem_normalizer_iff_map_conj_eq.mp (hn (mem_map_of_mem a hb))
  have hT := D.sourceOrbit_weakClosure_setup
  exact ⟨I,i,S,s,hw,hr,hOff,hA,hAT,hfix,hker,hcentral,hfive,hfour,
    fixed_normal_in_sylow D.sourceOrbit _ T hT.le_sylow inf_le_right hT.normalizes hnormalize,
    fixed_normalized_of_image_normalized D.sourceOrbit _ T inf_le_right hT.normalizes hnormalize,
    hc,a,hinj,hE,hmark⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
