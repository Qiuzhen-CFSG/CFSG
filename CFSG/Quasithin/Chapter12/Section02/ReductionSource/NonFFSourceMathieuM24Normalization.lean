module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuParabolicBender
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuParabolicNormalization
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Sieve
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceDihedralSelection
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Normalization of the original M24 cocode pair

The original four-element module image bounds the Bender field by its
Borel action. The full residual in H/O₂(H) is therefore PSL₂(4) or PSU₃(4),
with both covering centers eliminated. The proved unitary-torus argument
excludes the latter. The marked original pair has the same order as this
residual and hence covers it; lifting yields O²(I)=O²(H), T-normalization,
H=IT as a set product, and T-normalization of VA for the actual selected
w-offender. The existence endpoint constructs the offender and pair and
retains the original fixed three-space and all subgroup placements.

Source: Aschbacher--Smith 8.2.9(1--2), printed p.720, refs/quasithin.pdf.
The cocode marking remains an explicit earlier module-classification input.
The M24 code exclusion, other Mathieu rows, block and involution-centralizer
conclusions, and ambient J4 recognition remain with qt-d-1222-nonff-mathieu.
-/


public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode MathieuCode.TrioCalculation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.ParabolicReduction
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The full original residual is centerless PSL₂(4). The general Bender
field bound, full covering kernels and unitary exclusion are all discharged. -/
theorem sourceOrbit_m24_parabolic_residual_linear
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S)
    (hUZ : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    : let Q := pResidual 2 (H ⧸ pCore 2 H)
      center Q = ⊥ ∧ ClassicalGroup.IsPSL Q 2 4 := by
  obtain ⟨K,hK,hqs,hn,hgen,hm⟩ := D.sourceOrbit_m24_parabolic_normal_bender
    h hmany hV hq hnon a E hE hg hAT s hUZ hH
  let := hn
  obtain ⟨h28,_⟩ := D.sourceOrbit_m24_hstar_setup h hmany hV hq hnon hH
  have hVH := h28.le_sylow.trans h28.le_ambient
  let : IsElementaryAbelian 2 (D.sourceOrbit.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  obtain ⟨R,hR,hP,hM⟩ := h28.minimal
  obtain ⟨hVR,_,_,hout⟩ := intrinsic_source_data h28 R hR hP hM
  let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
  have hIC : I ≤ centralizer (U : Set G) := by
    apply le_centralizer_iff.mpr
    intro z hz x hx
    obtain ⟨w,hw,rfl⟩ := s.intersection_central (hUZ.le hz)
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨x,hx⟩)
  obtain ⟨_,hTU,_⟩ := D.sourceOrbit_m24_fixedPlane_local_of_offender_of_many
    h hmany hV hq hnon a E hE hg hAT
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [←selected_generates_hstar s hH]
    exact sup_le (hIC.trans (Subgroup.centralizer_le_normalizer _)) hTU
  have hUn : U ≠ ⊥ := fun he => s.intersection_ne_bot (hUZ.symm.trans he)
  have hMV : H ⊓ normalizer (L : Set G) ≤ normalizer (D.sourceOrbit : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans hHU)).trans
      (inf_normalizer_le_of_trivial_intersections
        (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti hUn
        (show U ≤ D.sourceOrbit from inf_le_left))
  have hmax : ChapterB.minimalParabolicMax R hP ≤
      normalizer (D.sourceOrbit.subgroupOf H : Set H) := by
    rw [←hM,←subgroupOf_normalizer_eq hVH]
    intro x hx
    exact hMV ⟨x.property,hx⟩
  obtain ⟨_,_,_,_,hparam,_⟩ := D.sourceOrbit_m24_cocode_geometry_of_many
    h hmany hV hq hnon a E hE hg
  have hs : ¬Group.IsSolvable H := by
    intro hh
    let := hh
    have hb := generationParameter_le_one_of_solvable (G := H)
    rw [hparam H hH] at hb
    omega
  have hS : (R : Subgroup H) = (T.subtype hH.1.1.2 : Subgroup H) := hR
  have hgenR : K ⊔ (R : Subgroup H) = ⊤ := hS.symm ▸ hgen
  have hJ : ChapterB.minimalParabolicCore R hP = localCore (normalizer (L : Set G)) H := by
    change (ChapterB.minimalParabolicMax R hP).normalCore = _
    rw [←hM]
  have hmR : ClassificationModels.IsBenderModel
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore R hP))) := by
    let c := QuotientGroup.quotientMulEquivOfEq hJ
    have hc : (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore R hP))).map
        c.toMonoidHom = K.map (QuotientGroup.mk' (localCore (normalizer (L : Set G)) H)) := by
      rw [map_map]
      congr 1
    let b := ((K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore R hP))).equivMapOfInjective
      c.toMonoidHom c.injective).trans (MulEquiv.subgroupCongr hc)
    exact hm.of_mulEquiv b
  obtain ⟨_,hfour,_⟩ := D.sourceOrbit_m24_pair_parabolic_quotient
    h hmany hV hq hnon a E hE hg hAT s hUZ hH
  have hmodel := MathieuSieve.source_bender_field_four R hP hs K hK hgenR hmR
    (D.sourceOrbit.subgroupOf H) hVR hout hmax hfour.le
  obtain ⟨hQ,_,⟨e⟩⟩ := MathieuSieve.residual_center_quotient_of_normal_component
    R hP hs K hK hqs hgenR
  let Q := pResidual 2 (H ⧸ pCore 2 H)
  let : IsQuasisimple Q := hQ
  have hmodels : ClassicalGroup.IsPSL (Q ⧸ center Q) 2 4 ∨
      ClassicalGroup.IsPSU (Q ⧸ center Q) 3 4 := by
    rcases hmodel with ⟨F,hF,hfin,hsize,⟨f⟩⟩ | ⟨F,hF,hfin,J,hsize,hconj,⟨f⟩⟩
    · exact .inl ⟨F,hF,hfin,hsize,⟨e.trans f⟩⟩
    · exact .inr ⟨F,hF,hfin,J,hsize,hconj,⟨e.trans f⟩⟩
  have hcore : pCore 2 Q = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : Q.Normal).isSubnormal,
      pCore_quotient_pCore_eq_bot,MonoidHom.comap_bot,(MonoidHom.ker_eq_bot_iff Q.subtype).mpr Q.subtype_injective]
  obtain ⟨hz,hl | hu⟩ := MathieuSieve.field_four_cover_models Q hcore hmodels
  · exact ⟨hz,hl⟩
  · exact (D.sourceOrbit_m24_not_unitary_four_residual h hmany hV hq hnon a E hE
      hg hAT s hUZ hH hu).elim

/-- The SAME original pair fills the full residual in H/O₂(H). -/
theorem sourceOrbit_m24_parabolic_quotient_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S)
    (hUZ : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    : pResidual 2 (H ⧸ pCore 2 H) =
      (I.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) := by
  obtain ⟨_,F,hF,hfin,hsize,⟨eR⟩⟩ := D.sourceOrbit_m24_parabolic_residual_linear
    h hmany hV hq hnon a E hE hg hAT s hUZ hH
  obtain ⟨⟨eI⟩,hle⟩ := D.sourceOrbit_m24_pair_parabolic_residual
    h hmany hV hq hnon a E hE hg hAT s hUZ hH
  obtain ⟨aR⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hsize
  obtain ⟨aI⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (show Nat.card (BenderSuzuki.PFAppendixIII.BinaryGaloisField 2) = 4 from
      GaloisField.card 2 2 (by decide))
  exact (eq_of_le_of_card_ge hle
    (Nat.card_congr ((eR.trans aR).trans (eI.trans aI).symm).toEquiv).le).symm

/-- Source 8.2.9(1–2) for the original marked M24 cocode pair, with the
quotient sieve and all residual-lifting premises discharged. -/
theorem sourceOrbit_m24_pair_normalization
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S)
    (hUZ : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    : (pResidual 2 I).map I.subtype = (pResidual 2 H).map H.subtype ∧
      (T : Subgroup G) ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) ∧
      (T : Subgroup G) ≤ normalizer (I : Set G) ∧
      (H : Set G) = (I : Set G) * (T : Set G) ∧
      (T : Subgroup G) ≤ normalizer
        ((D.sourceOrbit ⊔ (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓
          I.pCoreIn 2) : Subgroup G) : Set G) := by
  exact MathieuPair.selected_normalization_of_quotient_cover s hH
    D.sourceOrbit_weakClosure_setup.normalizes
    (D.sourceOrbit_m24_parabolic_quotient_cover h hmany hV hq hnon a E hE hg hAT s hUZ hH).le

/-- Construct the compatible pair and its normalization while preserving
the original offender's fixed three-space and the actual selected offender. -/
theorem sourceOrbit_m24_fixedPlane_normalized_pair
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T)
    : let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
      ∃ (H I : Subgroup G) (i : I) (S : Sylow 2 I),
        H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        H ≤ centralizer (U : Set G) ⊔ (T : Subgroup G) ∧
        H ≤ normalizer (U : Set G) ∧ generationParameter H = 2 ∧
        Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S ∧
        IsWOffenderAt D.sourceOrbit (T : Subgroup G) i.val⁻¹ ∧
        offenderNormalizer D.sourceOrbit i.val⁻¹ =
          D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 ∧
        offenderNormalizer D.sourceOrbit i.val⁻¹ ≤ T ∧
        U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
        U = D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G) ∧
        I ≤ centralizer (U : Set G) ∧
        (pResidual 2 I).map I.subtype = (pResidual 2 H).map H.subtype ∧
        (T : Subgroup G) ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) ∧
        (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        (H : Set G) = (I : Set G) * (T : Set G) ∧
        (T : Subgroup G) ≤ normalizer
          ((D.sourceOrbit ⊔ offenderNormalizer D.sourceOrbit i.val⁻¹ : Subgroup G) : Set G) := by
  obtain ⟨H,I,i,S,hH,hHC,hHU,_,hn,s,ho,ha,ht,hUZ,hUF,hIC⟩ :=
    D.sourceOrbit_m24_fixedPlane_compatible_pair h hmany hV hq hnon a E hE hg hAT
  obtain ⟨hr,hTR,hTI,hprod,hVA⟩ :=
    D.sourceOrbit_m24_pair_normalization h hmany hV hq hnon a E hE hg hAT s hUZ hH
  rw [←ha] at hVA
  exact ⟨H,I,i,S,hH,hHC,hHU,hn,s,ho,ha,ht,hUZ,hUF,hIC,hr,hTR,hTI,hprod,hVA⟩

/-- The original Sylow-positioned offender, compatible pair and its
source 8.2.9 normalization are constructed together. -/
theorem sourceOrbit_m24_exists_normalized_pair
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    : ∃ g : G, IsWOffenderAt D.sourceOrbit (T : Subgroup G) g ∧
      offenderNormalizer D.sourceOrbit g ≤ T ∧
      let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
      ∃ (H I : Subgroup G) (i : I) (S : Sylow 2 I),
        H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        H ≤ centralizer (U : Set G) ⊔ (T : Subgroup G) ∧
        H ≤ normalizer (U : Set G) ∧ generationParameter H = 2 ∧
        Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S ∧
        IsWOffenderAt D.sourceOrbit (T : Subgroup G) i.val⁻¹ ∧
        offenderNormalizer D.sourceOrbit i.val⁻¹ =
          D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 ∧
        offenderNormalizer D.sourceOrbit i.val⁻¹ ≤ T ∧
        U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
        U = D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G) ∧
        I ≤ centralizer (U : Set G) ∧
        (pResidual 2 I).map I.subtype = (pResidual 2 H).map H.subtype ∧
        (T : Subgroup G) ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) ∧
        (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        (H : Set G) = (I : Set G) * (T : Set G) ∧
        (T : Subgroup G) ≤ normalizer
          ((D.sourceOrbit ⊔ offenderNormalizer D.sourceOrbit i.val⁻¹ : Subgroup G) : Set G) := by
  obtain ⟨g,hg,hAT,_⟩ :=
    D.sourceOrbit_m24_exists_fixedPlane_local_of_many h hmany hV hq hnon a E hE
  exact ⟨g,hg,hAT,D.sourceOrbit_m24_fixedPlane_normalized_pair
    h hmany hV hq hnon a E hE hg hAT⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
