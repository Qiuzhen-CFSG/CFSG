module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeOddProductsApplication
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeParabolicDegree
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeCubicResidualModels
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeParabolicImage
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourDiagramLift
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourBinaryExclusion
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceDihedralSelection
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Pair

/-!
# The original nonsolvable M22-code parabolic

The quintet section of the supplied pair bounds both odd ranks in H. Its
cubic quotient gives the original order-two marked image; constructing
selected pairs from inverted rotations then forces every such rotation to
have order three. The cubic residual sieve identifies the full two-residual
of H/O₂(H) with PSL₃(2), preserving the original maximal overlap and Sylow.

Long-root placement puts the original marker inside this residual. The
core-free diagram witness lifts to an element of the original Sylow acting
by a noninner automorphism on the same full residual.
The internal M24-pair import reuses its general non-FF normalization and
quadratic-ratio helpers on this original Mathieu orbit.

Source: Aschbacher–Smith 8.2.9, printed pp.720–721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.SmallOvergroups
open Chapter8.Section02.MathieuShadowRows MathieuCode.M22Quintet.CocodeTransfer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- The odd-rank bounds come from the actual supplied pair and its quintet
section, without replacing its conjugator or pair subgroup. -/
theorem sourceOrbit_m22_code_selected_parabolic_odd_ranks
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S) :
    primeRank 3 H ≤ 1 ∧ primeRank 5 H ≤ 1 := by
  obtain ⟨_,_,_,_,hcent,_,hfour,_,hTU,hcomm,_,_,_,f,_,hsection,_⟩ :=
    D.sourceOrbit_m22_code_selected_cubic_data h hmany hV hnon d hH s
  let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hfour
    rw [hz,Representation.BinaryOffender.rank_bot] at hfour
    omega
  have hlocal : IsTwoLocal (normalizer (U : Set G)) :=
    ⟨U,hUne,(IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le inf_le_left,rfl⟩
  have hthin := (h.simpleQTKE.twoLocal_sqtk hlocal).stronglyQuasithin
  exact selected_m22_code_parabolic_odd_ranks s hH D.sylow_normalizes_component
    hcent D.sylow_normalizes_component hTU hcomm hsection hthin

/-- The full nonsolvable two-residual on the original H is the binary
PSL₃(2) model, retaining its actual maximal overlap and diagram witness. -/
theorem sourceOrbit_m22_code_selected_nonsolvable_binary_diagram
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (hsol : ¬Group.IsSolvable H) :
    IsEGenerated 1 H ∧ generationParameter H = 1 ∧
    ((normalizer (L : Set G)).subgroupOf H).normalCore = pCore 2 H ∧
    let q := QuotientGroup.mk' (pCore 2 H)
    let M := ((normalizer (L : Set G)).subgroupOf H).map q
    let Tplus := ((T : Subgroup G).subgroupOf H).map q
    ∃ K : Subgroup (H ⧸ pCore 2 H), IsComponent (H ⧸ pCore 2 H) K ∧
      K.IsCComponent ∧ K.Normal ∧ pResidual 2 (H ⧸ pCore 2 H) = K ∧
      center K = ⊥ ∧ K ⊔ Tplus = ⊤ ∧ SingleClauses M K Tplus ∧
      ClassicalGroup.IsPSL K 3 2 ∧ DiagramModel M K Tplus 1 := by
  have hpair := D.sourceOrbit_m22_code_selected_small_quotient h hmany hV hnon d hH s
  obtain ⟨h3,h5⟩ := D.sourceOrbit_m22_code_selected_parabolic_odd_ranks h hmany hV hnon d hH s
  obtain ⟨_,_,himage,hgen,hpar⟩ :=
    D.sourceOrbit_m22_code_pair_core_image h hmany hV hnon d hH s h3 h5 hpair
  have hrot := (D.sourceOrbit_m22_code_odd_rotations_of_image_two
    h hmany hV hnon d hH himage).1
  have h28 := (D.sourceOrbit_m22_code_hstar_setup h hmany hV hnon d hH).1
  have hVH := h28.le_sylow.trans h28.le_ambient
  let : IsElementaryAbelian 2 (D.sourceOrbit.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  obtain ⟨R,hR,hP,hM⟩ := h28.minimal
  obtain ⟨hVR,_,_,hout⟩ := intrinsic_source_data h28 R hR hP hM
  have hmax : ChapterB.minimalParabolicMax R hP ≤
      normalizer (D.sourceOrbit.subgroupOf H : Set H) := by
    rw [←hM,←subgroupOf_normalizer_eq hVH]
    intro x hx
    exact D.m24_hstar_normalizes h hmany hV hnon hH ⟨x.property,hx⟩
  have hm := parabolic_quotient_cubic_residual_model h28.sqtk R hP hsol
    (D.sourceOrbit.subgroupOf H) hVR hout hmax himage h3 h5 hrot
  have hJ : ChapterB.minimalParabolicCore R hP =
      ((normalizer (L : Set G)).subgroupOf H).normalCore := by
    change (ChapterB.minimalParabolicMax R hP).normalCore = _
    rw [←hM]
  dsimp only at hm
  rw [hJ,←hM,hR] at hm
  exact ⟨hgen,hpar,hm⟩

/-- The binary residual's outer action is induced by an element of the
original Sylow, through the literal quotient map on the original H. -/
theorem sourceOrbit_m22_code_selected_nonsolvable_diagram_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (hsol : ¬Group.IsSolvable H) :
    IsEGenerated 1 H ∧ generationParameter H = 1 ∧
    ((normalizer (L : Set G)).subgroupOf H).normalCore = pCore 2 H ∧
    let q := QuotientGroup.mk' (pCore 2 H)
    let M := ((normalizer (L : Set G)).subgroupOf H).map q
    let Tplus := ((T : Subgroup G).subgroupOf H).map q
    ∃ K : Subgroup (H ⧸ pCore 2 H), IsComponent (H ⧸ pCore 2 H) K ∧
      K.IsCComponent ∧ K.Normal ∧ pResidual 2 (H ⧸ pCore 2 H) = K ∧
      center K = ⊥ ∧ K ⊔ Tplus = ⊤ ∧ SingleClauses M K Tplus ∧
      ClassicalGroup.IsPSL K 3 2 ∧ DiagramModel M K Tplus 1 ∧
      (D.sourceOrbit.subgroupOf H).map q ≤ K ∧
      ∃ t : H, (t : G) ∈ (T : Subgroup G) ∧ ∃ α : MulAut K,
        α ∉ MulAut.innerSubgroup K ∧
        (∀ k : K, (α k : H ⧸ pCore 2 H) = q t * (k : H ⧸ pCore 2 H) * (q t)⁻¹) := by
  obtain ⟨hgen,hpar,hcore,K,hcomp,hKC,hKN,hres,hcenter,hKT,hclauses,h2,hdiagram⟩ :=
    D.sourceOrbit_m22_code_selected_nonsolvable_binary_diagram h hmany hV hnon d hH s hsol
  let q := QuotientGroup.mk' (pCore 2 H)
  let M := ((normalizer (L : Set G)).subgroupOf H).map q
  let Tplus := ((T : Subgroup G).subgroupOf H).map q
  let := hKN
  have hMcore : sourceKernel M = ⊥ := image_normalCore_eq_bot _ _ hcore
  have h28 := (D.sourceOrbit_m22_code_hstar_setup h hmany hV hnon d hH).1
  have hVH := h28.le_sylow.trans h28.le_ambient
  let : IsElementaryAbelian 2 (D.sourceOrbit.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  obtain ⟨R,hR,hP,hM⟩ := h28.minimal
  obtain ⟨hVR,_,_,_⟩ := intrinsic_source_data h28 R hR hP hM
  let Sq := R.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  let W := (D.sourceOrbit.subgroupOf H).map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  have hk : q.ker ≤ (R : Subgroup H) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal R
  have hPq := ChapterB.minimalParabolic_surjective R hP q
    (QuotientGroup.mk'_surjective _) hk
  have hmax : ChapterB.minimalParabolicMax Sq hPq =
      (ChapterB.minimalParabolicMax R hP).map q :=
    (ChapterB.minimalParabolicMax_map_core R hP q (QuotientGroup.mk'_surjective _)
      (by simpa only [q,QuotientGroup.ker_mk'] using ChapterB.minimalParabolicTwoCore_le_core R hP)).symm
  have hRW : (R : Subgroup H) ≤ normalizer (D.sourceOrbit.subgroupOf H : Set H) := by
    rw [hR,←subgroupOf_normalizer_eq hVH]
    exact comap_mono D.sourceOrbit_weakClosure_setup.normalizes
  have hKq : K ⊔ (Sq : Subgroup (H ⧸ pCore 2 H)) = ⊤ := by
    change K ⊔ (R : Subgroup H).map q = ⊤
    rw [hR]
    exact hKT
  have hMqcore : (ChapterB.minimalParabolicMax Sq hPq).normalCore = ⊥ := by
    rw [hmax,←hM]
    exact hMcore
  have hWK := corefree_binary_marker_le_component Sq hPq K hKq hMqcore W
    (map_mono hVR) ((map_mono hRW).trans (le_normalizer_map q)) h2
  obtain ⟨tplus,α,hα,hact⟩ := corefree_diagram_actor_lift M K Tplus hMcore hdiagram
  obtain ⟨t,ht,hqt⟩ := tplus.property
  have hqt' : q t = (tplus : H ⧸ pCore 2 H) := hqt
  refine ⟨hgen,hpar,hcore,K,hcomp,hKC,hKN,hres,hcenter,hKT,hclauses,h2,hdiagram,hWK,
    t,ht,α,hα,?_⟩
  intro k
  rw [hqt']
  exact hact k

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
