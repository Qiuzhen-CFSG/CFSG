module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.HigherDegreeSource
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeDegree
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeParabolicSolvable
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourGeneration
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceDihedralSelection
import all CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve.SmallRows.LocalActions
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Excluding the four-group M22 parabolic image

A noncyclic image of the original elementary subgroup in the full star
quotient gives a genuine marked pair of degree greater than one. Every
geometric pair for the same full M22 code action has degree one, so this
is impossible. The star and two-core images have the same kernel on the
original Sylow subgroup. The image therefore has order two, and the
central marked involution supplies generation at one in the original H.

Source: Aschbacher--Smith 8.2.9, printed p.720, refs/quasithin.pdf.
The original selected pair is never replaced in the resulting image and
intersection conclusions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterB ChapterE HermitianSource Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

/-- The original full M22 code action excludes the noncyclic parabolic image
in the nonsolvable branch and forces generation parameter one. -/
theorem m22_code_nonsolvable_parabolic_image
    {V H M T : Subgroup G} [IsElementaryAbelian 2 V]
    (h : HypothesisE28 KnownSimple.IsKnownSimple H T M V)
    (hfit : generalizedFitting H = pCore 2 H)
    (hsol : ¬Group.IsSolvable H)
    (hMV : H ⊓ M ≤ normalizer (V : Set G))
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M)
    (ha : primeRank 2 (Automizer V) ≤ 5)
    (a : Automizer V →* MathieuCode.m22PairStabilizer) (hinj : Function.Injective a)
    (E : Additive V ≃ₗ[ZMod 2] MathieuCode.M22Code)
    (hE : ∀ b v, E (automizerRepresentation V b v) =
      MathieuCode.m22OuterCodeRepresentation (a b) (E v))
    (h3 : primeRank 3 H ≤ 1) (h5 : primeRank 5 H ≤ 1) :
    Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 ∧
      IsEGenerated 1 H ∧ generationParameter H = 1 := by
  have hVH := h.le_sylow.trans h.le_ambient
  let : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  obtain ⟨R,hR,hP,hM⟩ := h.minimal
  obtain ⟨hVR,hVN,hcore,hout⟩ := intrinsic_source_data h R hR hP hM
  have hMV' : minimalParabolicMax R hP ≤ normalizer (V.subgroupOf H : Set H) := by
    rw [←hM,←subgroupOf_normalizer_eq hVH]
    exact fun x hx => hMV ⟨x.property,hx⟩
  let W := (V.subgroupOf H).map (QuotientGroup.mk' (minimalParabolicCore R hP))
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hne : W ≠ ⊥ := by
    intro he
    have hh := (map_eq_bot_iff (V.subgroupOf H)).mp he
    exact hout (by simpa only [QuotientGroup.ker_mk'] using hh)
  have htwo : Nat.card W = 2 := by
    rcases two_or_four_of_elementary_ne_bot W hne with hc | hc
    · exact hc
    have hex := Witnesses.BenderPlacement.source_large_image_degree
      ChapterA.Section02.theoremA_knownSimple
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) h.sqtk R hP hsol
      (V.subgroupOf H) hVR hVN hcore hMV' hc h3 h5
    rw [←hM] at hex
    obtain ⟨n,w,hw⟩ := hex
    obtain ⟨I,i,S,s⟩ := geometric_selected_of_original_witness h hfit R hR w hq hTI hNV
    have he := s.m22_code_parameter_one ha a hinj E hE
    omega
  refine ⟨(Witnesses.BenderPlacement.twoCore_image_card_eq_star R hP (V.subgroupOf H) hVR).trans htwo,?_⟩
  exact parabolic_generation_one_of_star_involution h.sqtk R hP
    (V.subgroupOf H) hVR hMV' htwo

/-- The image bound applies to the supplied original pair and identifies
its literal two-core intersection without changing the chosen conjugator. -/
theorem selected_m22_code_nonsolvable_core_image
    {V H M I : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (h : HypothesisE28 KnownSimple.IsKnownSimple H T M V)
    (hfit : generalizedFitting H = pCore 2 H)
    (hsol : ¬Group.IsSolvable H)
    (hMV : H ⊓ M ≤ normalizer (V : Set G))
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M)
    (ha : primeRank 2 (Automizer V) ≤ 5)
    (a : Automizer V →* MathieuCode.m22PairStabilizer) (hinj : Function.Injective a)
    (E : Additive V ≃ₗ[ZMod 2] MathieuCode.M22Code)
    (hE : ∀ b v, E (automizerRepresentation V b v) =
      MathieuCode.m22OuterCodeRepresentation (a b) (E v))
    (h3 : primeRank 3 H ≤ 1) (h5 : primeRank 5 H ≤ 1) :
    I.pCoreIn 2 = I ⊓ H.pCoreIn 2 ∧
      V ⊓ I.pCoreIn 2 = V ⊓ H.pCoreIn 2 ∧
      Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 ∧
      IsEGenerated 1 H ∧ generationParameter H = 1 := by
  obtain ⟨hcard,hgen,hparameter⟩ := m22_code_nonsolvable_parabolic_image h hfit hsol hMV
    hq hTI hNV ha a hinj E hE h3 h5
  let B := V ⊓ I.pCoreIn 2
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hsmall : Nat.card ((B.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) ≤ 2 := by
    have hle : (B.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ≤
        (V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) :=
      map_mono (comap_mono inf_le_left)
    exact (Nat.le_of_dvd Nat.card_pos (card_dvd_of_le hle)).trans_eq hcard
  have hinter : B = V ⊓ H.pCoreIn 2 := by
    rcases Normalizer.ParabolicReduction.RankSieve.SmallRows.ambient_pair_intersection_alternatives
      V I B H hVI s.family.le_ambient rfl (selected_one_core_index s) hsmall with
      ⟨he,_⟩ | hfour
    · exact he
    · omega
  have hB : V ⊓ I.pCoreIn 2 ≤ H.pCoreIn 2 := by
    change B ≤ H.pCoreIn 2
    rw [hinter]
    exact inf_le_right
  have hP := selected_one_pair_core_in_hstar_core s hB
  exact ⟨hP,hinter,hcard,hgen,hparameter⟩

/-- Both original parabolic branches have the same literal pair kernel and
degree-one generation, without replacing the supplied selected pair. -/
theorem selected_m22_code_core_image
    {V H M I : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (h : HypothesisE28 KnownSimple.IsKnownSimple H T M V)
    (hfit : generalizedFitting H = pCore 2 H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hMV : H ⊓ M ≤ normalizer (V : Set G))
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M)
    (ha : primeRank 2 (Automizer V) ≤ 5)
    (a : Automizer V →* MathieuCode.m22PairStabilizer) (hinj : Function.Injective a)
    (E : Additive V ≃ₗ[ZMod 2] MathieuCode.M22Code)
    (hE : ∀ b v, E (automizerRepresentation V b v) =
      MathieuCode.m22OuterCodeRepresentation (a b) (E v))
    (h3 : primeRank 3 H ≤ 1) (h5 : primeRank 5 H ≤ 1)
    (hpair : Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2))) :
    I.pCoreIn 2 = I ⊓ H.pCoreIn 2 ∧
      V ⊓ I.pCoreIn 2 = V ⊓ H.pCoreIn 2 ∧
      Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 ∧
      IsEGenerated 1 H ∧ generationParameter H = 1 := by
  by_cases hsol : Group.IsSolvable H
  · obtain ⟨hcore,hinter,hcard⟩ := selected_m22_code_solvable_core_image s h hH hsol
      ((normal_subgroupOf_iff_le_normalizer h.le_sylow).mp h.normal_in_sylow) h3 hpair
    let := hsol
    have hgen : IsEGenerated 1 H := isEGenerated_one_of_solvable
    have heven : 2 ∣ Nat.card H := by
      have hd := (((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).card_subgroup_dvd_card).trans
        (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _))
      rwa [hcard] at hd
    exact ⟨hcore,hinter,hcard,hgen,(generationParameter_eq_one_iff_of_even heven).mpr hgen⟩
  · exact selected_m22_code_nonsolvable_core_image s h hfit hsol hMV hq hTI hNV
      ha a hinj E hE h3 h5

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
