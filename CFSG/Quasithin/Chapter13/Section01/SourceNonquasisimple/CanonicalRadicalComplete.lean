module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.HigherPrimaryComplete
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.SourceCompletion
public import Theory.GroupTheory.CComponent.OrbitNormalized

/-!
# Excluding activity of the canonical nonquasisimple radical

For X=Ξ_p(L), nonzero intrinsic action makes Y=N_L(O₂(XT))^∞ faithful
by A.4.10. The actual maximal-counterexample theorem then places every
characteristic normalizer of O₂(XT) in N_G(L), supplying the original
radical exclusion configuration.

The canonical escape gives a nonnormal maximal component K. Apply the
adequate embedding theorem inside KT. Its detected component belongs to
the T-orbit of K, so the invariant alternative would normalize K. The
remaining swapped alternatives contradict the proved even and odd
pushing-up exclusions. No general Chapter 10 normalization or full C.2.7
classification premise is used.

Source: Aschbacher--Smith 1.3.8, pp.512--514; A.4.10, p.60;
13.1.4(2),(5), p.867.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
open Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate Chapter1.RadicalNormalizers Chapter1.RadicalActions
open Chapter1.XiEmbedding Chapter1.RadicalExclusions Chapter1.RadicalExclusions.ModelReduction
open Chapter12.Section02 ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Activity of the canonical radical transfers to its actual normalizer residual. -/
theorem active_canonical_normalizerResidual_faithful
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hi : intrinsicSignalizerModule (XiP p L) ≠ ⊥) :
    normalizerResidual L (radicalCore p L T) ∈ nonquasisimpleFaithful T := by
  let h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have h38 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → B.Normal ∨ IsQuasisimple B :=
    fun _ _ _ hA hO _ hB => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hA hO hB
  have hr := residual_normalizer_data_of_source h36 h38 hL
    (uniqueness_local_quotient_sqtk hG hL.1.2.2) hn ho hd
  let X := XiP p L
  let Y := normalizerResidual L (radicalCore p L T)
  have hX := (XiP_mem_XiPlus_source hG T hL.1 hn ho hd).1
  have hHe := hX.mem_He
    (fun _ hM _ hN hNM hnorm => lemma_1_1_3_1 hM hN hNM hnorm)
    (lemma_1_1_4_6 T (hG.evenCharacteristic T))
  have hXt : IsSignalizerType X := ⟨hX.ne_bot,hX.perfect,
    generalizedFitting_eq_pCore_of_selfCentralizing 2 (mem_He_iff.mp hHe)⟩
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) := hX.invariant
  have hJY : Y ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) :=
    sup_le (Y_normalizes_XiP p p L T) hTX
  have hYt := mem_L_isSignalizerType T (hG.evenCharacteristic T) hr.Y_mem_L
  have hSyl : IsSylowIn 2 (T : Subgroup G) (Y ⊔ (T : Subgroup G)) := hr.Y_mem_L.2.1
  have hcore : (Y ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      (T : Subgroup G) ⊓ normalizer (X : Set G) := by
    apply le_inf _ ((pCoreIn_le 2 _).trans hJY)
    have hh := pCoreIn_le_sylow (Y ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using hh
  have hSylX : IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (X : Set G))
      ((Y ⊔ (T : Subgroup G)) ⊓ normalizer (X : Set G)) := by
    simpa only [inf_eq_left.mpr hTX,inf_eq_left.mpr hJY] using hSyl
  have hf := (SourceChains.source_A410 X Y (T : Subgroup G) hr.X_le_Y hXt hYt
    hr.t_normalizes_Y hSyl hcore hSylX).2.2 ⟨hXt,hi⟩
  exact ⟨(mem_faithfulLocalComponents_iff T Y).mpr ⟨hr.Y_mem_L,hf⟩,hr.Y_not_quasisimple⟩

/-- The active canonical radical supplies characteristic control for its original two-core. -/
theorem active_canonical_characteristic_control
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hi : intrinsicSignalizerModule (XiP p L) ≠ ⊥) :
    ((XiP p L ⊔ (T : Subgroup G)).pCoreIn 2).characteristicNormalizerClosure ≤
      normalizer (L : Set G) := by
  let Y := normalizerResidual L (radicalCore p L T)
  have hY := active_canonical_normalizerResidual_faithful h.simpleQTKE T hL hn ho hd hi
  obtain ⟨B,hB,hYB,hf,hbn,hmax,hjoin,hu,_⟩ := h.maximal_counterexample_of_many hmany hY
  obtain ⟨_,_,hM⟩ := RadicalConjugateRigidity.maximal_radical_structure h.simpleQTKE T hL hn ho hd
  have hTL := radicalLocal_invariant_source hL.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.2.2) hn
  have hYM : Y ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le ((normalizerResidual_le _ _).trans L.le_normalizer) hTL
  have he := hu (normalizer (L : Set G)) hM hYM
  apply characteristicNormalizerClosure_le_of_unique_twoLocal
    (radicalCore_isTwoGroup p L T)
    (sup_le (normalizerResidual_le_normalizer _ _) (t_le_normalizer_radicalCore p L T))
  intro N hN hYN
  exact (hu N hN hYN).trans he.symm

/-- The original Configuration is available whenever the canonical radical is active. -/
theorem active_canonical_configuration
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hi : intrinsicSignalizerModule (XiP p L) ≠ ⊥) (P : Sylow p (XiP p L)) :
    Configuration p T (XiP p L) ((P : Subgroup (XiP p L)).map (XiP p L).subtype)
      L (normalizer (L : Set G)) := by
  let h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have hQ := uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.2.2
  obtain ⟨hp,hs⟩ := XiP_oddQuotient_of_A36 h36 hL.1 hQ hn ho hd
  obtain ⟨_,hN,hM⟩ := RadicalConjugateRigidity.maximal_radical_structure
    h.simpleQTKE T hL hn ho hd
  exact ⟨Fact.out,ho,hp,(XiP_mem_XiPlus_source h.simpleQTKE T hL.1 hn ho hd).1,
    rfl,hL,hs,⟨P,rfl⟩,XiP_automizer_not_isCyclic_of_A36 h36 hL.1 hQ hn ho hd P,
    XiP_normalizer_irreducible_of_A36 h36 hL.1 hQ hn ho hd P,rfl,hN.symm,hM,
    active_canonical_characteristic_control h hmany hL hn ho hd hi⟩

/-- Every component in KT shares the original component's nonnormality under T. -/
private theorem component_moved_of_original_moved (T : Sylow 2 G)
    {K B : Subgroup G} (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hB : B ∈ cComponentsIn (K ⊔ (T : Subgroup G)))
    (hm : ¬ (T : Subgroup G) ≤ normalizer (K : Set G)) :
    ¬ (T : Subgroup G) ≤ normalizer (B : Set G) := by
  intro hn
  let H := K ⊔ (T : Subgroup G)
  let S := (T : Subgroup G).subgroupOf H
  have hgen : K.subgroupOf H ⊔ S = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  have hSB : S ≤ normalizer (B.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hB.1]
    intro s hs
    exact hn hs
  have he := hK.1.eq_of_pGroup_generated_of_normalized hB.2
    T.isPGroup'.comap_subtype hgen hSB
  have he' := congrArg (map H.subtype) he
  rw [map_subgroupOf_eq_of_le hB.1,map_subgroupOf_eq_of_le le_sup_left] at he'
  exact hm (he' ▸ hn)

/-- The canonical nonquasisimple radical has zero intrinsic module under the original source hypotheses. -/
theorem canonical_radical_intrinsicModule_eq_bot
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    intrinsicSignalizerModule (XiP p L) = ⊥ := by
  by_contra hi
  let P : Sylow p (XiP p L) := default
  have hc := active_canonical_configuration h hmany hL hn ho hd hi P
  obtain ⟨K,hf,hq,hXK,hm⟩ := canonical_radical_intrinsic_escape h hmany hL.1 hn ho hd hi
  have hXT : XiP p L ⊔ (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) :=
    sup_le (hXK.trans (componentOrbit_le_sup K T)) le_sup_right
  have hout := Configuration.initial_not_le_of_A36 h.simpleQTKE
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
      (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))) hc hf.1.1 hq hXT
  obtain ⟨B,hB⟩ := Configuration.exists_componentCandidate_knownSimple h.simpleQTKE T hc
    ⟨hf.1.1.2.2,fun _ ht => mem_sup_right ht⟩ hXT hout
  rcases hB.alternatives.2 with ⟨hs,hmodel⟩ | ⟨hTB,_⟩
  · exact (hB.toPushingUpComponent (ComponentCandidate.not_le_of_configuration hc hB)).false_of_swapped
      T hc (lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)) hs hmodel
  · exact component_moved_of_original_moved T hf.1.1 hB.component hm hTB

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
