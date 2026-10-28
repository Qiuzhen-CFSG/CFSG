module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeExclusion
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceBorel
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceActions
public import Theory.SpecificGroups.ProjectiveLinearThree

/-!
# The exchanged binary Borel and the original point cubic

For a moved PSL₂(2ⁿ) component of an original local I, source 1.2.2
identifies its actual Sylow orbit with O^{3′}(I). Its two components give
marked product coordinates in I/O₂(I). The Sylow intersection chooses the
Borel B₀, and the proved solvable-overgroup exclusion places B₀ in N_G(L)
and makes it normalize the original L₁. In particular L₁ lies in O²(B₀).

The same Borel's torus map has two-core kernel. Its image of L₁ is cubic,
and the actual moving element of T exchanges the torus factors. Invariance
therefore makes both projections injective. The Borel order forces n even.
Applying the construction to the complete nonnormal component catalogue
removes every odd field degree. No theta or A₆ flag hypothesis is used.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1056,
refs/quasithin.pdf; the intrinsic Borel transports are shared with 13.8.16(1).
The full-point comparison, field-four reduction and module contradiction
are separate source steps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The literal moved component orbit is the three-residual of the original
local. Normality and quotient simplicity are derived at the same local. -/
theorem local_binary_threeResidual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (Chapter13.Section08.Source.starImage I K) 2 (2 ^ n))
    (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K) :
    (primeToResidual 3 I).map I.subtype = conjugateSpanBy K (T : Subgroup G) := by
  have hTI := F.sylow_le_of_mem_Hz hI
  have hi : (normalizer (K.subgroupOf I : Set I)).index = 2 := by
    rcases Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
      (local_star_sqtk h I hI) hK with hn | hi
    · exact (hmoving (conjugateSpan_eq_of_normal I K T hKI hTI hn)).elim
    · exact hi.1
  have hm' := hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  let : IsQuasisimple ((K.subgroupOf I) ⧸ pCore 2 (K.subgroupOf I)) :=
    local_component_twoCore_isQuasisimple h hab structural previous faithful I hI _ hK
  let : IsSimpleGroup ((K.subgroupOf I) ⧸ pCore 2 (K.subgroupOf I)) := by
    obtain ⟨k, _, _, hk, ⟨e⟩⟩ := hm'
    have hlarge : 4 ≤ Nat.card k := by
      rw [hk]
      exact Nat.pow_le_pow_right (n := 2) (by decide) hn
    let : IsSimpleGroup PSL(2,k) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
    exact e.isSimpleGroup
  have hd : 3 ∣ Nat.card ((K.subgroupOf I) ⧸ pCore 2 (K.subgroupOf I)) := by
    obtain ⟨k, _, _, _, ⟨e⟩⟩ := hm'
    rw [Nat.card_congr e.toEquiv]
    exact Matrix.ProjectiveSpecialLinearGroup.three_dvd_card k 2 le_rfl
  have hr : primeRank 3 I ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 I) pCore_isPGroup]
    exact (local_star_sqtk h I hI).stronglyQuasithin 3 (by decide) (by decide)
  have he := Chapter1.Section02.nonnormal_component_threeResidual hK hi hd hr
    (.linear_even n hn hm')
  have he' := congrArg (map I.subtype) he
  rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hKI,
    ←MonoidHom.range_eq_map,range_subtype] at he'
  obtain ⟨t,ht,htn⟩ := exists_moving_element K (T : Subgroup G) hmoving
  rw [he',orbit_eq_two_conjugates I K I hKI le_rfl hi (hTI ht) htn,
    orbit_eq_two_conjugates I K T hKI hTI hi ht htn]

private theorem binary_point_parabolic_solvable
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    Group.IsSolvable (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) := by
  let B : Subgroup G := F.Li L 1 ⊔ (T : Subgroup G)
  let : Group.IsNilpotent (pCore 2 B) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  let : Group.IsSolvable (B ⧸ pCore 2 B) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (pointQuotientEquiv (F := F) h structural).toMonoidHom)
      (pointQuotientEquiv (F := F) h structural).injective
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 B)).mpr ⟨inferInstance,inferInstance⟩

/-- Construct the original Borel, its two-residual containment and the
diagonal cubic in its actual common torus coordinates. The product formula
retains the original moving element and both component inclusions. -/
theorem local_binary_borel
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (Chapter13.Section08.Source.starImage I K) 2 (2 ^ n))
    (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K) :
    ∃ (t : G) (htT : t ∈ (T : Subgroup G))
      (_htmove : t ∉ normalizer (K : Set G)),
    let N := K ⊔ K.conjBy t
    ∃ (hNI : N ≤ I)
      (e : Chapter13.Section08.Source.starImage I N ≃*
        Chapter13.Section08.Source.starImage I K × Chapter13.Section08.Source.starImage I K)
      (S : Sylow 2 (Chapter13.Section08.Source.starImage I N)),
      let Bstar := SylowBorel.relativeBorel (Chapter13.Section08.Source.starImage I N) S
      let B₀ := borelLift I N hNI Bstar
      let C := SourceActions.CommonTorus I N e S
      let f := SourceTorus.toCommonTori I N hNI e S hn hm
      let D := SourceActions.Markings.image B₀ (F.Li L 1) f
      conjugateSpanBy K (T : Subgroup G) = N ∧
      (∀ a b, (e.symm (a, b) : Chapter13.Section08.Source.Hstar I) =
        (a : Chapter13.Section08.Source.Hstar I) *
          (QuotientGroup.mk' (pCore 2 I) ⟨t, F.sylow_le_of_mem_Hz hI htT⟩ * b *
          (QuotientGroup.mk' (pCore 2 I) ⟨t, F.sylow_le_of_mem_Hz hI htT⟩)⁻¹)) ∧
      (primeToResidual 3 I).map I.subtype = N ∧
      (S : Subgroup _).map (Chapter13.Section08.Source.starImage I N).subtype =
        Chapter13.Section08.Source.starImage I ((T : Subgroup G) ⊓ N) ∧
      Chapter13.Section08.Source.starImage I B₀ = Bstar ∧
      Group.IsSolvable B₀ ∧ F.Li L 1 ≤ B₀ ∧ B₀ ≤ normalizer (L : Set G) ∧
      F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (B₀ : Set G) ∧
      B₀ ≤ normalizer (F.Li L 1 : Set G) ∧
      F.Li L 1 ≤ (pResidual 2 B₀).map B₀.subtype ∧
      Even n ∧ primeRank 3 B₀ = 2 ∧
      Nat.card D = 3 ∧
      Function.Injective (fun x : D => (x : C × C).1) ∧
      Function.Injective (fun x : D => (x : C × C).2) := by
  have hTI := F.sylow_le_of_mem_Hz hI
  have hLI := F.Li_one_le_of_mem_Hz hI
  have hi : (normalizer (K.subgroupOf I : Set I)).index = 2 := by
    rcases Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
      (local_star_sqtk h I hI) hK with hn | hi
    · exact (hmoving (conjugateSpan_eq_of_normal I K T hKI hTI hn)).elim
    · exact hi.1
  obtain ⟨t,ht,htn⟩ := exists_moving_element K (T : Subgroup G) hmoving
  have horbit := orbit_eq_two_conjugates I K T hKI hTI hi ht htn
  have hqs := (local_component_star_isComponent h hab structural previous faithful I hI _ hK).2
  let N := K ⊔ K.conjBy t
  have hNI : N ≤ I := horbit.ge.trans (conjugateSpanBy_le hKI (hTI.trans I.le_normalizer))
  have hres : (primeToResidual 3 I).map I.subtype = N :=
    (local_binary_threeResidual h hab structural previous faithful I K hI hKI hK hn hm hmoving).trans horbit
  have hnN : (N.subgroupOf I).Normal := by
    rw [←hres,subgroupOf,comap_map_eq_self_of_injective I.subtype_injective]
    infer_instance
  let := hnN
  obtain ⟨e₀,hcoord⟩ := exists_moving_star_coordinates I K hKI hK hqs (hTI ht) htn hm
  let e := e₀.symm
  have hSylow : Chapter1.IsSylowIn 2 (T : Subgroup G) I :=
    ⟨T.subtype hTI,by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTI]⟩
  have hLp : IsPPerfect 2 (F.Li L 1) := isPPerfect_embedded_pResidual 2 _
  have hL3 : IsPGroup 3 ((F.Li L 1) ⧸ pCore 2 (F.Li L 1)) :=
    IsPGroup.of_card (n := 1) (by simpa using pointResidual_core_quotient_card (F := F) h structural)
  let := binary_point_parabolic_solvable (F := F) h structural
  obtain ⟨S,hS,him,hsol,hLB,hBM,hnB⟩ := exists_source_borel
    I N (F.Li L 1) T F.H (normalizer (L : Set G)) hNI hLI hSylow e hn hm hLp hL3 hres
    (hNI.trans hI.2.1) ((sup_le hLI hTI).trans hI.2.1)
    (fun J hJ hJH hs => solvable_point_overgroup_le_normalizer d h hab structural previous faithful earlier J hJH hJ hs)
  let Bstar := SylowBorel.relativeBorel (Chapter13.Section08.Source.starImage I N) S
  let B₀ := borelLift I N hNI Bstar
  have hB₀H : B₀ ≤ F.H := (borelLift_le I N hNI Bstar).trans (hNI.trans hI.2.1)
  have hBN := point_normalized_solvable_normalizes_point d h hab structural previous faithful earlier B₀ hB₀H hsol hnB
  have hLres := embedded_pResidual_mono 2 hLB
  rw [(pResidual_eq_top_iff 2 _).mpr hLp,←MonoidHom.range_eq_map,range_subtype] at hLres
  have hLrank : primeRank 3 (F.Li L 1) ≠ 0 := by
    intro hz
    have hd : 3 ∣ Nat.card (F.Li L 1) := by
      have hh := card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 (F.Li L 1)))
        (QuotientGroup.mk'_surjective _)
      rwa [pointResidual_core_quotient_card (F := F) h structural] at hh
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz hd
  have hBrank := borelLift_threeRank I N hNI Bstar (SylowBorel.relativeBorel_le _ S)
  have hle : primeRank 3 (F.Li L 1) ≤ primeRank 3 B₀ :=
    Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hLB) (inclusion_injective hLB)
  have hthree : 3 ∣ Nat.card Bstar := by
    by_contra hh
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hh
    rw [hBrank,hz] at hle
    exact hLrank (Nat.eq_zero_of_le_zero hle)
  have heven := SylowBorel.even_of_three_dvd _ e S hn hm hthree
  let C := SourceActions.CommonTorus I N e S
  let f := SourceTorus.toCommonTori I N hNI e S hn hm
  let D := SourceActions.Markings.image B₀ (F.Li L 1) f
  have hTB : (T : Subgroup G) ≤ normalizer (B₀ : Set G) := le_sup_right.trans hnB
  let τ := SourceTorus.normalizerAction I N hNI e S hn hm ⟨t, hTB ht⟩
  have hτ := (SourceActions.source_factor_actions I K T hTI ht hNI hi htn e hcoord S hn hm hTB).1
  have hk : IsPGroup 2 f.ker := by
    rw [SourceTorus.toCommonTori_ker]
    exact pCore_isPGroup
  have ho := SourceActions.commonTori_odd I N e S hn hm
  have hD : Nat.card D = 3 :=
    (SourceActions.Markings.image_card B₀ (F.Li L 1) hLB f hk ho).trans
      (pointResidual_core_quotient_card (F := F) h structural)
  have hτD : D.map τ.toMonoidHom = D :=
    SourceActions.Markings.image_invariant B₀ (F.Li L 1) f ⟨t, hTB ht⟩
      (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural) ht) τ
      (SourceTorus.normalizerAction_toCommonTori I N hNI e S hn hm ⟨t, hTB ht⟩)
  exact ⟨t,ht,htn,hNI,e,S,horbit,hcoord,hres,
    hS.trans (starImage_inf_sylow I N T hSylow).symm,
    him,hsol,hLB,hBM,hnB,hBN,hLres,heven,
    hBrank.trans (SylowBorel.threeRank _ e S hn hm heven),hD,
    CartanAction.fst_injective τ hτ D hD hτD,
    CartanAction.snd_injective τ hτ D hD hτD⟩

/-- Applied to every original nonnormal component, the Borel construction
forces an even binary field degree, without a model or Borel hypothesis. -/
theorem local_nonnormal_component_even_binary
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ∃ n, 2 ≤ n ∧ Even n ∧
      ClassicalGroup.IsPSL (Chapter13.Section08.Source.starImage I K) 2 (2 ^ n) := by
  obtain ⟨n,hn,hm⟩ := local_nonnormal_component_binary d h hab structural previous faithful earlier
    I hI (K.subgroupOf I) hK hnormal
  have hm' := hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK).symm
  have hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K := by
    intro he
    exact hnormal (normal_of_sylow_span_eq I K T hKI (F.sylow_le_of_mem_Hz hI)
      ((Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
        (local_star_sqtk h I hI) hK).imp_right And.left) he)
  obtain ⟨t,ht,htm,hNI,e,S,horbit,hcoord,hres,hS,him,hsol,hLB,hBM,hnB,hBN,hLres,heven,_⟩ :=
    local_binary_borel d h hab structural previous faithful earlier I K hI hKI hK hn hm' hmoving
  exact ⟨n,hn,heven,hm'⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
