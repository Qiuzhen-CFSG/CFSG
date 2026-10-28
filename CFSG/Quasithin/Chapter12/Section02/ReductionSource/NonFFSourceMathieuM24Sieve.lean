module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuParabolicSieve
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceDihedralSelection
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Unitary
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve.Mathieu

/-!
# The actual M24 cocode parabolic has a normal Bender residual

The recognized GL₃(2) local factor contributes a cubic direction in the
original two-local normalizer, giving m₃(H)≤1. The selected pair supplies
three in |H/O₂(H)| and the literal image of the original module has order
four. TI at the same nonzero fixed three-space makes H∩N_G(L) normalize
that module. Together with the proved n(H)=2 these facts apply the full
non-Bender sieve to the original H and its original maximal core.

The full residual in H/O₂(H) is quasisimple, its center is exactly the
image of that core, and its central quotient is an actual Bender model.
All original pair, quotient, Sylow and module markings are retained.
The remaining field-four restriction, central-kernel elimination,
T-normalization, other Mathieu rows and ambient J4 recognition remain
with qt-d-1222-nonff-mathieu. This is not the full source 8.2.9 theorem.
Source: Aschbacher--Smith 8.2.9, printed p.720, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode MathieuCode.TrioCalculation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.ParabolicReduction
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual local GL₃(2) factor forces cubic rank at most one in H. -/
theorem sourceOrbit_m24_parabolic_three_rank
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
    : primeRank 3 H ≤ 1 := by
  let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
  let R := localResidual L U
  have hIC : I ≤ centralizer (U : Set G) := by
    apply le_centralizer_iff.mpr
    intro z hz x hx
    obtain ⟨w,hw,rfl⟩ := s.intersection_central (hUZ.le hz)
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨x,hx⟩)
  obtain ⟨_,_,⟨e⟩,_,hn,hcomm,_⟩ :=
    D.sourceOrbit_m24_fixedPlane_component_recognition h hmany hV hq hnon a E hE hg hAT
  obtain ⟨_,hTU,hlocal,_⟩ := D.sourceOrbit_m24_fixedPlane_local_of_offender_of_many
    h hmany hV hq hnon a E hE hg hAT
  have hHN : H ≤ normalizer (U : Set G) := by
    rw [←selected_generates_hstar s hH]
    exact sup_le (hIC.trans (Subgroup.centralizer_le_normalizer _)) hTU
  have hjoin : H ⊔ R ≤ normalizer (U : Set G) :=
    sup_le hHN ((localResidual_le L U).trans inf_le_right)
  have hr : primeRank 3 (H ⊔ R : Subgroup G) ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hjoin) (inclusion_injective hjoin)).trans
      ((h.simpleQTKE.twoLocal_sqtk hlocal).stronglyQuasithin 3 (by decide) (by decide))
  have hIM : ¬ I ≤ normalizer (L : Set G) := by
    intro hi
    apply hH.1.2
    rw [←selected_generates_hstar s hH]
    exact sup_le hi D.sylow_normalizes_component
  exact RankSieve.Mathieu.cocode_three_rank_le_one T L (normalizer (L : Set G)) H I U
    hH s.family.le_ambient hIM hIC D.sylow_normalizes_component hTU hcomm
    (e.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm) hr

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode MathieuCode.TrioCalculation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.ParabolicReduction
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The exhaustive source sieve selects a normal Bender component in the original H. -/
theorem sourceOrbit_m24_parabolic_normal_bender
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
    : ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K.Normal ∧ K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤ ∧
      ClassificationModels.IsBenderModel
        (K.map (QuotientGroup.mk' (localCore (normalizer (L : Set G)) H))) := by
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
  have hn : 1 < generationParameter H := by rw [hparam H hH]; decide
  have h3 := D.sourceOrbit_m24_parabolic_three_rank h hmany hV hq hnon a E hE hg hAT s hUZ hH
  obtain ⟨_,hfour,_⟩ := D.sourceOrbit_m24_pair_parabolic_quotient
    h hmany hV hq hnon a E hE hg hAT s hUZ hH
  obtain ⟨⟨b⟩,_⟩ := D.sourceOrbit_m24_pair_parabolic_residual
    h hmany hV hq hnon a E hE hg hAT s hUZ hH
  have hd : 3 ∣ Nat.card ((I.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) := by
    rw [Nat.card_congr b.toEquiv]
    exact BenderSuzuki.MatrixGroups.three_dvd_card_psl2_char_two _
  obtain ⟨K,hK,hqs,hKn,hKT,hmodel⟩ := MathieuSieve.source_normal_bender_component h28.sqtk
    R hP hn h3 (hd.trans (card_subgroup_dvd_card _)) (D.sourceOrbit.subgroupOf H)
    hVR hout hmax hfour.le
  have hS : (R : Subgroup H) = (T.subtype hH.1.1.2 : Subgroup H) := hR
  rw [hS] at hKT
  change ClassificationModels.IsBenderModel
    (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicMax R hP).normalCore)) at hmodel
  rw [←hM] at hmodel
  exact ⟨K,hK,hqs,hKn,hKT,hmodel⟩

/-- The quotient sieve on the literal original H/O₂(H), including its
full residual and the image of the original maximal core. -/
theorem sourceOrbit_m24_parabolic_residual_bender
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
      IsQuasisimple Q ∧
        (localCore (normalizer (L : Set G)) H).map (QuotientGroup.mk' (pCore 2 H)) =
          (center Q).map Q.subtype ∧ ClassificationModels.IsBenderModel (Q ⧸ center Q) := by
  obtain ⟨K,hK,hqs,hn,hgen,hm⟩ := D.sourceOrbit_m24_parabolic_normal_bender
    h hmany hV hq hnon a E hE hg hAT s hUZ hH
  let := hn
  obtain ⟨h28,_⟩ := D.sourceOrbit_m24_hstar_setup h hmany hV hq hnon hH
  obtain ⟨R,hR,hP,hM⟩ := h28.minimal
  have hS : (R : Subgroup H) = (T.subtype hH.1.1.2 : Subgroup H) := hR
  have hgenR : K ⊔ (R : Subgroup H) = ⊤ := hS.symm ▸ hgen
  have hs : ¬Group.IsSolvable H := by
    intro hh
    let := hh
    obtain ⟨_,_,_,_,hparam,_⟩ := D.sourceOrbit_m24_cocode_geometry_of_many
      h hmany hV hq hnon a E hE hg
    have htwo := hparam H hH
    have hb := generationParameter_le_one_of_solvable (G := H)
    omega
  obtain ⟨hQ,hZ,⟨e⟩⟩ := MathieuSieve.residual_center_quotient_of_normal_component
    R hP hs K hK hqs hgenR
  have hJ : ChapterB.minimalParabolicCore R hP = localCore (normalizer (L : Set G)) H := by
    change (ChapterB.minimalParabolicMax R hP).normalCore = _
    rw [←hM]
  rw [hJ] at hZ
  let c := QuotientGroup.quotientMulEquivOfEq hJ
  have hc : (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore R hP))).map
      c.toMonoidHom = K.map (QuotientGroup.mk' (localCore (normalizer (L : Set G)) H)) := by
    rw [map_map]
    congr 1
  let b := ((K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore R hP))).equivMapOfInjective
    c.toMonoidHom c.injective).trans (MulEquiv.subgroupCongr hc)
  exact ⟨hQ,hZ,hm.of_mulEquiv (e.trans b)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
