module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPushingUp
public import CFSG.Quasithin.ChapterC.Section02.SourceHypotheses
public import Theory.GroupTheory.SylowCentralizerOfNormalizer
public import Theory.GroupTheory.PCoreRestriction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuCocodeBounds
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryCoverPlacement
public import CFSG.Quasithin.Chapter4.Section02.Unitary.SourceSetup
-- Internal proof continuation: unfold the original component-action map only.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPairCentralizers

/-!
# Constructing the original Mathieu pushing-up subgroups

At the original vector x, take H=C_G(x), M=N_G(L), Q=O₂(LT), and
B=C_L(x)^∞. The original uniqueness and even-characteristic hypotheses give
SQTK for H, a nontrivial ambient two-core, F*(H∩M)=O₂(H∩M), and the literal
characteristic-normalizer control for Q. The orbit lies in Z(Q).

The marked M23 and M24 cocodes give O₂(C_LT(x))=Q, normal C-component
status for B in H∩M, B/O₂(B)≃M22, [W,B]=W≤B, and O₂(BQ)=Q.
The M24 proof keeps the full Aut(M22) point quotient before taking B.
The native residual action puts the section centralizer in C_G(W), whose
Sylow subgroup is the original Q. Restriction supplies the final Sylow
clause of C.2.8 on the source subgroups without conjugating x.
The subsequent C.4.8 exclusion, ambient containment, remaining Mathieu
rows and J4 assembly remain with
qt-d-1222-nonff-mathieu. No pair-containment premise is assumed here.
Source: Aschbacher--Smith, 8.1.1, printed pp.712--713; C.2.8, p.147,
refs/quasithin.pdf.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuPairs
open Sporadic.Mathieu MathieuCode ChapterE
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The non-Sylow local conditions of C.2.8 on the actual vector centralizer. -/
theorem sourceOrbit_point_pushingUp_local
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (x : D.sourceOrbit) (hx : x ≠ 1) :
    let H := centralizer ({(x : G)} : Set G)
    let M := normalizer (L : Set G)
    let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
    IsSQTK KnownSimple.IsKnownSimple H ∧ H.pCoreIn 2 ≠ ⊥ ∧
      generalizedFitting (H ⊓ M : Subgroup G) = pCore 2 (H ⊓ M : Subgroup G) ∧
      Q ≤ H ⊓ M ∧
      (Q.subgroupOf H).characteristicNormalizerClosure ≤ (H ⊓ M).subgroupOf H ∧
      D.sourceOrbit ≤ (center Q).map Q.subtype ∧
      H ⊓ normalizer (D.sourceOrbit : Set G) ≤ H ⊓ M := by
  let H := centralizer ({(x : G)} : Set G)
  let M := normalizer (L : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hpow : (x : G)^2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) x.property
  have hxG : (x : G) ≠ 1 := fun he => hx (Subtype.ext he)
  have ho : orderOf (x : G) = 2 := orderOf_eq_prime hpow hxG
  have hlocal : IsTwoLocal H := isTwoLocal_involution_centralizer ho
  have hQW : Q ≤ centralizer (D.sourceOrbit : Set G) := hV ▸ D.core_centralizes
  have hWQ : D.sourceOrbit ≤ Q := hV ▸ D.le_core
  have hQH : Q ≤ H := hQW.trans (centralizer_le (Set.singleton_subset_iff.mpr x.property))
  have hJM : L ⊔ (T : Subgroup G) ≤ M := sup_le L.le_normalizer D.sylow_normalizes_component
  have hQM : Q ≤ M := (pCoreIn_le 2 _).trans hJM
  have hcoreMQ : M.pCoreIn 2 ≤ Q := by
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 M)
    · have hMT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
        have hh := pCoreIn_le_sylow M (T.subtype D.sylow_normalizes_component)
        change M.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf M).map M.subtype at hh
        rwa [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ M from D.sylow_normalizes_component)] at hh
      exact hMT.trans le_sup_right
    · exact hJM.trans (M.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image M (pCore 2 M)))
  have hMH : H ⊓ M ∈ Chapter1.He G := by
    refine Chapter1.lemma_1_1_4_4 (N := H ⊓ M) ?_ inf_le_right
      (Chapter1.twoLocal_mem_He_of_sylow_le T (h.simpleQTKE.evenCharacteristic T)
        (D.doubledNormalizer_unique h).1.1 D.sylow_normalizes_component) ?_
    · intro he
      have hxQ := hWQ x.property
      have hxM : (x : G) ∈ H ⊓ M := ⟨hQH hxQ,hQM hxQ⟩
      exact hxG (mem_bot.mp (he ▸ hxM))
    · exact inf_le_left.trans (hcoreMQ.trans (le_inf hQH hQM))
  refine ⟨h.simpleQTKE.twoLocal_sqtk hlocal,Chapter1.mem_H_of_isTwoLocal hlocal,
    generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp hMH),
    le_inf hQH hQM,?_,?_,inf_le_inf_left H (D.sourceOrbit_normalizer_le h.toHypothesis1221)⟩
  · have hc := characteristicNormalizerClosure_subgroupOf_le hQH
      (D.sourceOrbit_core_characteristic_control h)
    intro g hg
    exact ⟨g.property,hc hg⟩
  · intro w hw
    refine ⟨⟨w,hWQ hw⟩,mem_center_iff.mpr ?_,rfl⟩
    intro q
    exact Subtype.ext (mem_centralizer_iff.mp (hQW q.property) w hw).symm

/-- For every distinguished M23 vector, its residual is the literal normal
C-component of the local intersection, and the original Q is retained. -/
theorem sourceOrbit_m23_pushingUp_seed_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ∃ a : Automizer D.sourceOrbit ≃* M23,
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode,
        (∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
          m23CocodeRepresentation (a b) (E v)) ∧
        ∀ x : D.sourceOrbit, E (Additive.ofMul x) ∈ m23WeightTwoOrbit →
          let H := centralizer ({(x : G)} : Set G)
          let M := normalizer (L : Set G)
          let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
          let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
          ((L ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2 = Q ∧
          (B.subgroupOf (H ⊓ M)).Normal ∧
          (B.subgroupOf (H ⊓ M)).IsCComponent ∧
          Nonempty ((B ⧸ pCore 2 B) ≃* M22) ∧
          conjugateSpanBy B (H ⊓ M) = B ∧
          D.sourceOrbit ≤ B ∧ ⁅D.sourceOrbit,B⁆ = D.sourceOrbit ∧
          (B ⊔ Q).pCoreIn 2 = Q := by
  obtain ⟨a,E,hE,hpairs⟩ := D.sourceOrbit_m23_pair_quotients_of_many h hmany hV hq hnon
  refine ⟨a,E,hE,?_⟩
  intro x hx
  obtain ⟨⟨e⟩,hcomm⟩ := hpairs x hx
  let H := centralizer ({(x : G)} : Set G)
  let M := normalizer (L : Set G)
  let C := L ⊓ H
  let B := (solvableResidual C).map C.subtype
  have hCA : C ≤ H ⊓ M := le_inf inf_le_right (inf_le_left.trans L.le_normalizer)
  have hn : H ⊓ M ≤ normalizer (C : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans H.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  obtain ⟨hN,hB,hqB,hspan⟩ := embedded_residual_component hCA hn e
  have hWB : D.sourceOrbit ≤ B := by
    have hWA : D.sourceOrbit ≤ H ⊓ M := le_inf
      ((le_centralizer D.sourceOrbit).trans
        (centralizer_le (Set.singleton_subset_iff.mpr x.property)))
      (D.sourceOrbit_weakClosure_setup.le_sylow.trans D.sylow_normalizes_component)
    rw [←hcomm]
    exact le_normalizer_iff_commutator_le_right.mp
      (hWA.trans ((normal_subgroupOf_iff_le_normalizer
        ((map_subtype_le _).trans hCA)).mp hN))
  have hcore := m23_pointCentralizer_core D.sourceOrbit L (L ⊔ (T : Subgroup G))
    D.sourceOrbit_component_normalizes le_sup_left
    (sup_le D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes)
    (hV ▸ D.core_centralizes) a
    (D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (Or.inl hq)) E hE x hx
  refine ⟨hcore,hN,hB,hqB,hspan,hWB,hcomm,?_⟩
  have hBK : B ≤ (L ⊔ (T : Subgroup G)) ⊓ H :=
    (map_subtype_le _).trans (inf_le_inf_right H le_sup_left)
  have hKA : (L ⊔ (T : Subgroup G)) ⊓ H ≤ H ⊓ M :=
    le_inf inf_le_right (inf_le_left.trans
      (sup_le L.le_normalizer D.sylow_normalizes_component))
  have hKB := hKA.trans ((normal_subgroupOf_iff_le_normalizer
    ((map_subtype_le _).trans hCA)).mp hN)
  have hh := normal_core_join B ((L ⊔ (T : Subgroup G)) ⊓ H) hBK hKB
  rwa [hcore] at hh

/-- The M24 cocode supplies the same residual construction, retaining its
full outer point quotient before taking the solvable residual. -/
theorem sourceOrbit_m24_pushingUp_seed_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (x : D.sourceOrbit) (hx : E (Additive.ofMul x) ∈ weightTwoOrbit) :
    let H := centralizer ({(x : G)} : Set G)
    let M := normalizer (L : Set G)
    let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
    let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ((L ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2 = Q ∧
      (B.subgroupOf (H ⊓ M)).Normal ∧
      (B.subgroupOf (H ⊓ M)).IsCComponent ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* M22) ∧
      conjugateSpanBy B (H ⊓ M) = B ∧
      D.sourceOrbit ≤ B ∧ ⁅D.sourceOrbit,B⁆ = D.sourceOrbit ∧
      (B ⊔ Q).pCoreIn 2 = Q := by
  obtain ⟨⟨e⟩,hcomm⟩ := D.sourceOrbit_m24_pair_quotient h.toHypothesis1221 hq a E hE x hx
  let H := centralizer ({(x : G)} : Set G)
  let M := normalizer (L : Set G)
  let C := L ⊓ H
  let B := (solvableResidual C).map C.subtype
  have hCA : C ≤ H ⊓ M := le_inf inf_le_right (inf_le_left.trans L.le_normalizer)
  have hn : H ⊓ M ≤ normalizer (C : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans H.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  obtain ⟨hN,hB,hqB,hspan⟩ := embedded_outer_residual_component hCA hn e
  have hWB : D.sourceOrbit ≤ B := by
    have hWA : D.sourceOrbit ≤ H ⊓ M := le_inf
      ((le_centralizer D.sourceOrbit).trans
        (centralizer_le (Set.singleton_subset_iff.mpr x.property)))
      (D.sourceOrbit_weakClosure_setup.le_sylow.trans D.sylow_normalizes_component)
    rw [←hcomm]
    exact le_normalizer_iff_commutator_le_right.mp
      (hWA.trans ((normal_subgroupOf_iff_le_normalizer
        ((map_subtype_le _).trans hCA)).mp hN))
  have hcore := m24_pointCentralizer_core D.sourceOrbit L (L ⊔ (T : Subgroup G))
    D.sourceOrbit_component_normalizes le_sup_left
    (sup_le D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes)
    (hV ▸ D.core_centralizes) a
    (D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (Or.inr hq)) E hE x hx
  refine ⟨hcore,hN,hB,hqB,hspan,hWB,hcomm,?_⟩
  have hBK : B ≤ (L ⊔ (T : Subgroup G)) ⊓ H :=
    (map_subtype_le _).trans (inf_le_inf_right H le_sup_left)
  have hKA : (L ⊔ (T : Subgroup G)) ⊓ H ≤ H ⊓ M :=
    le_inf inf_le_right (inf_le_left.trans
      (sup_le L.le_normalizer D.sylow_normalizes_component))
  have hKB := hKA.trans ((normal_subgroupOf_iff_le_normalizer
    ((map_subtype_le _).trans hCA)).mp hN)
  have hh := normal_core_join B ((L ⊔ (T : Subgroup G)) ⊓ H) hBK hKB
  rwa [hcore] at hh
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuPairs
open Sporadic.Mathieu MathieuCode ChapterE
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

private theorem point_C28
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (x : D.sourceOrbit) (hx : x ≠ 1)
    (B : Subgroup G) (hB : B ≤ centralizer ({(x : G)} : Set G) ⊓ normalizer (L : Set G))
    (hn : (B.subgroupOf (centralizer ({(x : G)} : Set G) ⊓ normalizer (L : Set G))).Normal)
    (hc : (B.subgroupOf (centralizer ({(x : G)} : Set G) ⊓ normalizer (L : Set G))).IsCComponent)
    (hspan : conjugateSpanBy B (centralizer ({(x : G)} : Set G) ⊓ normalizer (L : Set G)) = B)
    (hWB : D.sourceOrbit ≤ B) (hm : ⁅D.sourceOrbit,B⁆ = D.sourceOrbit)
    (hcore : (B ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2).pCoreIn 2 =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hsection : ChapterA.Section04.twoSectionCentralizer B
      (centralizer ({(x : G)} : Set G) ⊓ normalizer (L : Set G)) ≤
      centralizer (D.sourceOrbit : Set G)) :
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple
      (centralizer ({(x : G)} : Set G))
      (centralizer ({(x : G)} : Set G) ⊓ normalizer (L : Set G)) B
      ((L ⊔ (T : Subgroup G)).pCoreIn 2) D.sourceOrbit := by
  let H := centralizer ({(x : G)} : Set G)
  let M := normalizer (L : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  change (B ⊔ Q).pCoreIn 2 = Q at hcore
  let Y := ChapterA.Section04.twoSectionCentralizer B (H ⊓ M)
  let C := centralizer (D.sourceOrbit : Set G)
  obtain ⟨hsq,hne,hfit,hQ,hnorm,hcentral,hnW⟩ := D.sourceOrbit_point_pushingUp_local h hV x hx
  have hNB : H ⊓ M ≤ normalizer (B : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hB).mp hn
  have hQY : Q ≤ Y := by
    apply (ChapterA.Section04.le_twoSectionCentralizer_iff B (H ⊓ M) Q).mpr
    refine ⟨hQ,hQ.trans hNB,?_⟩
    have hQB : B ≤ normalizer (Q : Set G) := by
      rw [←hcore]
      exact (show B ≤ B ⊔ Q from le_sup_left).trans
        ((B ⊔ Q).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image (B ⊔ Q) (pCore 2 (B ⊔ Q : Subgroup G))))
    have hcomm : ⁅B,Q⁆ ≤ B ⊓ Q := le_inf
      (le_normalizer_iff_commutator_le_left.mp (hQ.trans hNB))
      (le_normalizer_iff_commutator_le_right.mp hQB)
    have hh := inf_pCoreIn_le_of_le 2 (show B ≤ B ⊔ Q from le_sup_left)
    rw [hcore] at hh
    exact hcomm.trans hh
  obtain ⟨P,hP⟩ := T.exists_centralizer_sylow_of_normalizes D.sourceOrbit
    D.sourceOrbit_weakClosure_setup.normalizes
  have hPQ : (P : Subgroup C).map C.subtype = Q := by
    rw [hP]
    simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  have hPR : (P : Subgroup C) ≤ (inclusion hsection).range := by
    intro c hc
    have hcQ : (c : G) ∈ Q := hPQ ▸ mem_map_of_mem C.subtype hc
    exact ⟨⟨c,hQY hcQ⟩,rfl⟩
  let S : Sylow 2 Y := P.comapOfInjective (inclusion hsection) (inclusion_injective hsection) hPR
  have hS : (S : Subgroup Y).map Y.subtype = Q := by
    ext g
    constructor
    · rintro ⟨s,hs,rfl⟩
      exact hPQ ▸ mem_map_of_mem C.subtype hs
    · intro hg
      obtain ⟨c,hc,rfl⟩ := hPQ.symm ▸ hg
      exact ⟨⟨c,hQY (hPQ ▸ mem_map_of_mem C.subtype hc)⟩,hc,rfl⟩
  refine ⟨hsq,isPGroup_pCoreIn 2 _,hQ,inf_le_left,hfit,hne,hB,hc,?_,hnorm,
    D.sourceOrbit_weakClosure_setup.nontrivial,inferInstance,?_,?_,?_,hnW⟩
  · rw [hspan]
    exact ⟨S,hS⟩
  · simpa only [hspan] using hWB
  · simpa only [hspan] using hm.symm
  · rw [hspan]
    change D.sourceOrbit ≤ (center ((B ⊔ Q).pCoreIn 2)).map _
    rw [hcore]
    exact hcentral

/-- Every distinguished vector in the surviving M23 cocode supplies the
literal original C.2.8 configuration, including its section-centralizer Sylow. -/
theorem sourceOrbit_m23_hypothesisC28_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ∃ a : Automizer D.sourceOrbit ≃* M23,
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode,
        (∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
          m23CocodeRepresentation (a b) (E v)) ∧
        ∀ x : D.sourceOrbit, E (Additive.ofMul x) ∈ m23WeightTwoOrbit →
          let H := centralizer ({(x : G)} : Set G)
          let M := normalizer (L : Set G)
          let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
          ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ M) B
            ((L ⊔ (T : Subgroup G)).pCoreIn 2) D.sourceOrbit ∧
            Nonempty ((B ⧸ pCore 2 B) ≃* M22) := by
  obtain ⟨a,E,hE,hseed⟩ := D.sourceOrbit_m23_pushingUp_seed_of_many h hmany hV hq hnon
  refine ⟨a,E,hE,?_⟩
  intro x hx
  obtain ⟨_,hn,hc,hquot,hspan,hWB,hm,hcore⟩ := hseed x hx
  have hx1 : x ≠ 1 := by
    intro he
    apply m23WeightTwoOrbit_nonzero hx
    rw [he]
    exact E.map_zero
  let H := centralizer ({(x : G)} : Set G)
  let M := normalizer (L : Set G)
  have hCA : L ⊓ H ≤ H ⊓ M := le_inf inf_le_right (inf_le_left.trans L.le_normalizer)
  have hBA := (map_subtype_le (solvableResidual (L ⊓ H : Subgroup G))).trans hCA
  have hAN : H ⊓ M ≤ normalizer (D.sourceOrbit : Set G) := by
    rw [inf_comm]
    exact inf_elementCentralizer_le_normalizer_of_trivial_intersections
      (D.sourceOrbit_hypothesisE61_of_many h hmany hnon hV).ti x.property
      (fun he => hx1 (Subtype.ext he))
  refine ⟨D.point_C28 h hV x hx1 _ hBA hn hc hspan hWB hm hcore ?_,hquot⟩
  exact m23_pair_section_le D.sourceOrbit L (H ⊓ M)
    D.sourceOrbit_component_normalizes hAN a
    (D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (Or.inl hq)) E hE x hx inf_le_left hCA
    ((normal_subgroupOf_iff_le_normalizer hBA).mp hn)

/-- The M24 cocode gives the same original C.2.8 configuration, using the
full outer point stabilizer in the section-centralizer calculation. -/
theorem sourceOrbit_m24_hypothesisC28_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (x : D.sourceOrbit) (hx : E (Additive.ofMul x) ∈ weightTwoOrbit) :
    let H := centralizer ({(x : G)} : Set G)
    let M := normalizer (L : Set G)
    let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ M) B
      ((L ⊔ (T : Subgroup G)).pCoreIn 2) D.sourceOrbit ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* M22) := by
  obtain ⟨_,hn,hc,hquot,hspan,hWB,hm,hcore⟩ :=
    D.sourceOrbit_m24_pushingUp_seed_of_many h hmany hV hq hnon a E hE x hx
  have hx1 : x ≠ 1 := by
    intro he
    apply weightTwoOrbit_nonzero hx
    rw [he]
    exact E.map_zero
  let H := centralizer ({(x : G)} : Set G)
  let M := normalizer (L : Set G)
  have hCA : L ⊓ H ≤ H ⊓ M := le_inf inf_le_right (inf_le_left.trans L.le_normalizer)
  have hBA := (map_subtype_le (solvableResidual (L ⊓ H : Subgroup G))).trans hCA
  have hAN : H ⊓ M ≤ normalizer (D.sourceOrbit : Set G) := by
    rw [inf_comm]
    exact inf_elementCentralizer_le_normalizer_of_trivial_intersections
      (D.sourceOrbit_hypothesisE61_of_many h hmany hnon hV).ti x.property
      (fun he => hx1 (Subtype.ext he))
  refine ⟨D.point_C28 h hV x hx1 _ hBA hn hc hspan hWB hm hcore ?_,hquot⟩
  exact m24_pair_section_le D.sourceOrbit L (H ⊓ M)
    D.sourceOrbit_component_normalizes hAN a
    (D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (Or.inr hq)) E hE x hx inf_le_left hCA
    ((normal_subgroupOf_iff_le_normalizer hBA).mp hn)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
