module

public import Theory.GroupTheory.Gaschutz
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.Interfaces
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.FusionReduction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Elementary
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.AmbientElementary
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.FAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.InitialFusion

/-!
# Assembly of the Case II normalizer and involution conclusions

The proved F-normalizer implication supplies the initial fusion input to
the E-normalizer argument. That argument constructs the A6 quotient and
fuses the marked involution with d, discharging the F-normalizer hypothesis.
Transitivity of the two normalizers covers all five involution representatives.

The coordinate Sylow restricts to a Sylow subgroup of each actual normalizer.
Transporting its explicit complements through those restrictions lets
Gaschütz's theorem split E and F in their ambient normalizers. The quotient
identifications then identify the actual complements with A6 and S5.
The final theorem discharges every premise of the conditional assembly.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemmas 1–7, pp.4–7.
-/

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

omit [Finite G] in
private theorem fusion_of_normalizer_orbit (A : Subgroup G) (hz : D.z ∈ A)
    (h : ∀ x y : A, x ≠ 1 → y ≠ 1 →
      ∃ g : normalizer (A : Set G), (g : G) * x * (g : G)⁻¹ = y)
    (x : G) (hx : x ∈ A) (hne : x ≠ 1) : IsConj x D.z := by
  have hx1 : (⟨x, hx⟩ : A) ≠ 1 := fun he => hne (congrArg Subtype.val he)
  have hz1 : (⟨D.z, hz⟩ : A) ≠ 1 := fun he => D.z_ne_one (congrArg Subtype.val he)
  obtain ⟨g, hg⟩ := h ⟨x,hx⟩ ⟨D.z,hz⟩ hx1 hz1
  exact isConj_iff.mpr ⟨g,hg⟩

/-- The two actual normalizer orbits suffice to fuse all ambient involutions.
This is conditional on the ambient normalizer conclusions, not a construction
of those conclusions from the Case II hypothesis. -/
public theorem involution_fusion_of_normalizer_actions
    (hE : ENormalizerAction D k) (hF : FNormalizerAction D k)
    (x : G) (hx : orderOf x = 2) : IsConj x D.z := by
  have hEmem (i : Fin 4) : CaseII.into D k (CaseII.z i) ∈ CaseII.E D k := by
    rw [← CaseII.modelE_map D k]
    exact mem_map_of_mem _ (CaseII.z_mem_modelE i)
  have hFmem (v : TwistedModel) (hv : v ∈ CaseII.modelF) :
      CaseII.into D k v ∈ CaseII.F D k := by
    rw [← CaseII.modelF_map D k]
    exact mem_map_of_mem _ hv
  have hEz : D.z ∈ CaseII.E D k := CaseII.into_z_zero D k ▸ hEmem 0
  have hFz : D.z ∈ CaseII.F D k :=
    CaseII.into_z_zero D k ▸ hFmem _ CaseII.modelF_generators.1
  have hne (v : TwistedModel) (hv : orderOf v = 2) : CaseII.into D k v ≠ 1 := by
    intro he
    have hv1 : v = 1 := CaseII.into_injective D k (he.trans (map_one _).symm)
    simp [hv1] at hv
  exact CaseII.involution_fusion_of_representatives D k
    (fusion_of_normalizer_orbit D _ hEz hE.fusion _ (hEmem 1) (hne _ (CaseII.z_order 1)))
    (fusion_of_normalizer_orbit D _ hEz hE.fusion _ (hEmem 2) (hne _ (CaseII.z_order 2)))
    (fusion_of_normalizer_orbit D _ hFz hF.fusion _ (hFmem _ CaseII.modelF_generators.2.2.1)
      (hne _ CaseII.actor_orders.1))
    (fusion_of_normalizer_orbit D _ hFz hF.fusion _ (hFmem _ CaseII.modelF_generators.2.2.2)
      (hne _ CaseII.actor_orders.2.2.2)) x hx

/-- Conditional assembly after the two ambient actions and both splitting
witnesses have been constructed. The source theorem must discharge all four
premises. -/
public theorem involutionNormalizerData_of_actions_and_complements
    (hE : ENormalizerAction D k) (hF : FNormalizerAction D k)
    (hEsplit : ∃ K : Subgroup (normalizer (CaseII.E D k : Set G)),
      ((CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G))).IsComplement' K)
    (hFsplit : ∃ K : Subgroup (normalizer (CaseII.F D k : Set G)),
      ((CaseII.F D k).subgroupOf (normalizer (CaseII.F D k : Set G))).IsComplement' K) :
    InvolutionNormalizerData D k := by
  refine ⟨?_, ?_, involution_fusion_of_normalizer_actions D k hE hF⟩
  · obtain ⟨K, hK⟩ := hEsplit
    obtain ⟨e⟩ := hE.quotient
    exact ⟨K, hK, ⟨hK.symm.QuotientMulEquiv.symm.trans e⟩⟩
  · obtain ⟨K, hK⟩ := hFsplit
    obtain ⟨e⟩ := hF.quotient
    exact ⟨K, hK, ⟨hK.symm.QuotientMulEquiv.symm.trans e⟩⟩

private theorem normalizer_complement_of_sylow_complement
    (A : Subgroup G) [IsElementaryAbelian 2 A] (P : Sylow 2 G)
    (hPN : (P : Subgroup G) ≤ normalizer (A : Set G))
    (hsplit : ∃ K : Subgroup P, (A.subgroupOf (P : Subgroup G)).IsComplement' K) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      (A.subgroupOf (normalizer (A : Set G))).IsComplement' K := by
  let N := normalizer (A : Set G)
  let V := A.subgroupOf N
  let Q : Sylow 2 N := P.subtype hPN
  let e : Q ≃* P := subgroupOfEquivOfLe hPN
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf A.le_normalizer
  apply (exists_complement_iff_sylow V (IsElementaryAbelian.isPGroup 2 V) Q).mpr
  obtain ⟨K, hK⟩ := hsplit
  refine ⟨K.comap e.toMonoidHom, isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_⟩
  · apply disjoint_def.mpr
    intro x hxV hxK
    apply e.injective
    rw [map_one]
    exact disjoint_def.mp hK.disjoint hxV hxK
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨⟨a, b⟩, he⟩ := hK.2 (e x)
    refine ⟨e.symm a, ?_, e.symm b, ?_, ?_⟩
    · exact a.property
    · change e (e.symm b) ∈ K
      rw [e.apply_symm_apply]
      exact b.property
    · apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using he

/-- Janko's Case II involution-normalizer conclusions: the actual E and F
normalizers split over E and F with complements isomorphic to A6 and S5,
and every ambient involution is conjugate to the marked involution.
The arbitrary coordinate equivalence need not preserve `D.sylow`. -/
public theorem involutionNormalizerData_of_caseII [IsSimpleGroup G] :
    InvolutionNormalizerData D k := by
  have hF := fNormalizerAction_of_caseII D k
  obtain ⟨hE, hd⟩ := eNormalizerAction_and_actorFusion D k
    (initial_fusion_of_caseII D k hF) hF
  apply involutionNormalizerData_of_actions_and_complements D k hE (hF hd)
  · let := CaseII.E_elementary D k
    exact normalizer_complement_of_sylow_complement (CaseII.E D k) (CaseII.caseIISylow D k)
      (CaseII.caseIISylow_le_normalizer_E D k) (CaseII.E_sylow_complement D k)
  · let := CaseII.F_elementary D k
    exact normalizer_complement_of_sylow_complement (CaseII.F D k) (CaseII.caseIISylow D k)
      (CaseII.caseIISylow_le_normalizer_F D k) (CaseII.F_sylow_complement D k)

end Theory.GroupTheory.HeldM22A10.M22Identification
