module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.SmallQuotients
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Source.Complete
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RankOneBlocks
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Classification
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.ConcreteSource

/-!
# The binary swapped branch from its actual Sylow geometry

The binary Borel normalizers in the two-factor quotient force the original
odd complement P to normalize T ∩ ⟨K^T⟩. The Frattini factorization
X = O₂(X)P then makes this intersection normal in XT, hence contained in
R = O₂(XT). Consequently R is Sylow in KR. The proved Sylow case of
C.2.7 constructs K's actual block; the solvable local image excludes its
A₅ alternative. C.1.9 and the centerless-factor theorem complete the
binary-branch contradiction.

The original component record supplies its own detected component and
orbit-action data through the nontrivial odd intersection P ∩ K. No new
block, Sylow or full-C.2.7 classification premise is introduced. The genuine
characteristic-normalizer control in Configuration and PushingUpSetup
remains an earlier source obligation, as does the odd-prime rank-one branch.

Source: Aschbacher–Smith, proof of Proposition 1.3.8, printed pp.513–514;
C.1.29 and C.2.7(3)(a), pp.134 and146.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open Chapter1 Chapter1.XiEmbedding Chapter1.RadicalExclusions
open Chapter1.RadicalExclusions.ModelReduction
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem simple_binary {Q : Type*} [Group Q]
    (hq : IsQuasisimple Q) {n : ℕ} (_hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL Q 2 (2^n)) : IsSimpleGroup Q := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let _ := hq
  let _ : Group.IsPerfect PSL(2,F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hs : IsSimpleGroup PSL(2,F) :=
    MulAction.IwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top
      PSL2.Iwasawa inferInstance
  exact e.isSimpleGroup_congr.mpr hs

private theorem candidate_detection
    {p : ℕ} {T X P M H K : Subgroup G}
    (h : ComponentCandidate KnownSimple.IsKnownSimple p T X P M H K)
    (hs : SwappedFactors T P K) (hm : SwappedModel p (XiQuotient K)) :
    ComponentDetection P H K := by
  let : Fact p.Prime := ⟨h.local_input.prime⟩
  let B := K.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let D := B.map q
  let eK := subgroupOfEquivOfLe h.component.1
  let eQ := QuotientGroup.congr (pCore 2 B) (pCore 2 K) eK (pCore_map_iso 2 eK)
  let e : XiQuotient K ≃* D := eQ.symm.trans (cComponentTwoCoreQuotientEquiv h.component.2)
  let : IsQuasisimple D := h.quasisimple.of_mulEquiv e
  let : IsSimpleGroup D := e.symm.isSimpleGroup_congr.mpr
    (swappedModel_simple h.quasisimple hm)
  have hD : IsComponent (XiQuotient H) D := ⟨h.component.2.subnormal.quotient,inferInstance⟩
  have hz : center D = ⊥ := by
    exact (inferInstance : (center D).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative D (center_eq_top_iff.mp he))
  refine ⟨h.component,h.quasisimple,hD,?_⟩
  intro hcomm
  have hcommH : ⁅B,P.subgroupOf H⁆ ≤ pCore 2 H := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    simpa only [B,map_commutator,map_subgroupOf_eq_of_le h.component.1,
      map_subgroupOf_eq_of_le h.local_input.complement_le_overgroup,pCoreIn] using hcomm
  have hzero : ⁅D,(P.subgroupOf H).map q⁆ = ⊥ := by
    rw [← map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hcommH
  have hdis : Disjoint P (H.pCoreIn 2) :=
    h.local_input.odd_complement.isPGroup.disjoint_of_coprime (isPGroup_pCoreIn 2 H)
      (Nat.coprime_two_right.mpr h.local_input.odd)
  have hi : P ⊓ K = ⊥ := by
    apply bot_unique
    intro x hx
    let xH : H := ⟨x,h.component.1 hx.2⟩
    let xD : D := ⟨q xH,mem_map_of_mem q hx.2⟩
    have hc : xD ∈ center D := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (((commutator_eq_bot_iff_le_centralizer.mp hzero) y.property)
        (q xH) (mem_map_of_mem q hx.1)).symm
    have he : q xH = 1 := congrArg Subtype.val (show xD = 1 from mem_bot.mp (hz ▸ hc))
    exact hdis.le_bot ⟨hx.1,mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff xH).mp he)⟩
  have hc := swapped_intersection_card h.alternatives.1 hs
  rw [hi,card_bot] at hc
  have hp := h.local_input.prime.one_lt
  omega

private theorem candidate_swapped_input
    {p : ℕ} {T X P M H K : Subgroup G}
    (h : ComponentCandidate KnownSimple.IsKnownSimple p T X P M H K)
    (hs : SwappedFactors T P K) (hm : SwappedModel p (XiQuotient K)) :
    SwappedSylowInput KnownSimple.IsKnownSimple p T X P H K := by
  let hd := candidate_detection h hs hm
  exact {
    toLocalInput := h.local_input
    sqtk := h.setup.sqtk
    component := h.component
    quasisimple := h.quasisimple
    orbit_normal := h.local_input.detected_component_orbit_normal h.setup.sqtk h.sylow_two hd
    complement_le_orbit := h.local_input.complement_le.trans h.containment
    orbit_commutator := h.local_input.detected_component_orbit_commutator_source h.setup.sqtk h.sylow_two hd
    noncentral := hd.noncentral_component_core
    not_invariant := hs.1
    sylow_two := h.sylow_two }

theorem binary_swapped_orbit_sylow_le_core
    {p : ℕ} {T X P H K : Subgroup G}
    (h : SwappedSylowInput KnownSimple.IsKnownSimple p T X P H K)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL (XiQuotient K) 2 (2^n)) :
    T ⊓ componentOrbit K T ≤ (X ⊔ T).pCoreIn 2 := by
  have hindex : (K.subgroupOf H).Normal ∨
      (normalizer (K.subgroupOf H : Set H)).index = 2 := by
    let := pCore_isNilpotent (p := 2) (G := H)
    apply cComponent_normal_or_index_two_of_quotient h.component.2 (pCore 2 H)
    have hsq : IsSQTK KnownSimple.IsKnownSimple (XiQuotient H) :=
      ⟨quotient_stronglyQuasithin h.sqtk.stronglyQuasithin,h.sqtk.isKGroup.quotient _⟩
    exact ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
      (ChapterA.Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
      hsq (pCore_quotient_pCore_eq_bot 2) (h.component.2.map_quotient _)
  have hi := hindex.resolve_left (fun hk => h.not_invariant
    ((le_sup_right.trans h.overgroup).trans
      ((normal_subgroupOf_iff_le_normalizer h.component.1).mp hk)))
  obtain ⟨e⟩ := SwappedFactorsProof.quotient_product
    ChapterA.Section03.CComponentCommutation.universal_A_3_7 h.toSwappedInput hi
      (simple_binary h.quasisimple hn hm)
  obtain ⟨S,hS⟩ := SwappedSylow.orbit_quotient_sylow h
  let U := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let A := (SwappedSylow.imageInOrbit K T P).map e.toMonoidHom
  have hU : (U : Subgroup _) = (SwappedSylow.imageInOrbit K T T).map e.toMonoidHom := by
    change (S : Subgroup _).map e.toMonoidHom = _
    rw [hS]
  let : Group.IsSolvable (A ⊔ (U : Subgroup _) : Subgroup _) := by
    have he : A ⊔ (U : Subgroup _) =
        (SwappedSylow.imageInOrbit K T P ⊔ SwappedSylow.imageInOrbit K T T).map e.toMonoidHom := by
      rw [Subgroup.map_sup,hU]
    rw [he]
    let := SwappedSylow.quotient_solvable h.toSwappedInput
    exact Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective _)
  have hAN := SwappedSylow.binary_model_prod_le_normalizer hn hm U A
  have hnorm : SwappedSylow.imageInOrbit K T P ≤
      normalizer (SwappedSylow.imageInOrbit K T T) := by
    apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [Subgroup.map_normalizer_eq_of_bijective _ e.bijective]
    change A ≤ normalizer ((U : Subgroup (XiQuotient K × XiQuotient K)) :
      Set (XiQuotient K × XiQuotient K)) at hAN
    rw [hU] at hAN
    exact hAN
  have hPN := SwappedSylow.normalizes_two_of_quotient h hnorm
  have hTN : T ≤ normalizer (T ⊓ componentOrbit K T : Subgroup G) := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    exact ⟨(mem_normalizer_iff.mp (T.le_normalizer ht) x).mp hx.1,
      (mem_normalizer_iff.mp (le_normalizer_componentOrbit K T ht) x).mp hx.2⟩
  have hXN : X ≤ normalizer (T ⊓ componentOrbit K T : Subgroup G) := by
    rw [← h.complement]
    exact sup_le (h.core_le_two_group.trans hTN) hPN
  exact le_pCoreIn_of_normalizes (h.two_group.to_le inf_le_left)
    (inf_le_left.trans le_sup_right) (sup_le hXN hTN)

theorem binary_swapped_core_sylow
    {p : ℕ} {T X P H K : Subgroup G}
    (h : SwappedSylowInput KnownSimple.IsKnownSimple p T X P H K)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL (XiQuotient K) 2 (2^n))
    (hr : (X ⊔ T).pCoreIn 2 ≤ normalizer K) :
    IsSylowIn 2 ((X ⊔ T).pCoreIn 2) (K ⊔ (X ⊔ T).pCoreIn 2) := by
  let R := (X ⊔ T).pCoreIn 2
  have hSR : T ⊓ K ≤ R :=
    (inf_le_inf_left T (le_componentOrbit K T)).trans
      (binary_swapped_orbit_sylow_le_core h hn hm)
  have hSK := isSylowIn_iff.mp (SwappedSylow.component_sylow h)
  refine isSylowIn_iff.mpr ⟨isPGroup_pCoreIn 2 _,le_sup_right,?_⟩
  intro U hU hRU hUKR
  have he : U ⊓ K = T ⊓ K := hSK.2.2 _ (hU.to_le inf_le_left)
    (le_inf (hSR.trans hRU) inf_le_right) inf_le_right
  apply le_antisymm _ hRU
  intro u hu
  have hprod : u ∈ (K : Set G) * (R : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left K R hr]
    exact hUKR hu
  obtain ⟨k,hk,r,hrR,hkr⟩ := hprod
  have hkU : k ∈ U := by
    have hh := U.mul_mem hu (U.inv_mem (hRU hrR))
    rwa [← hkr,mul_inv_cancel_right] at hh
  rw [← hkr]
  exact R.mul_mem (hSR (he ▸ (show k ∈ U ⊓ K from ⟨hkU,hk⟩))) hrR

/-- In the binary branch, the actual C.2.3 setup supplies the block without
the full eight-case C.2.7 classification. -/
theorem binary_swapped_block_of_pushingUp_setup
    {p : ℕ} {T X P H K M : Subgroup G}
    (h : SwappedSylowInput KnownSimple.IsKnownSimple p T X P H K)
    (hH : H ∈ HOver G (T : Set G)) (hp : 3 < p)
    (hs : FullSieve.SourceInterface.Input KnownSimple.IsKnownSimple H
      ((X ⊔ T).pCoreIn 2) (H ⊓ M) K)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL (XiQuotient K) 2 (2^n)) :
    BinaryBlockEmbedding p T X P H K := by
  have hSylow := binary_swapped_core_sylow h hn hm hs.normalizes
  obtain ⟨hb,hchi⟩ := ChapterC.C27Source.source_chiZero_of_sylow_input hs hSylow
  obtain ⟨he,hf,hmodel⟩ := SwappedSylow.embedding_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A)) h
  have hX : X ≤ componentOrbit K T := h.toLocalInput.le_of_complement_le
    h.complement_le_orbit ((normal_subgroupOf_iff_le_normalizer
      (SwappedSylow.orbit_le_overgroup h.toSwappedInput)).mp h.orbit_normal)
  let hc : ComponentCandidate KnownSimple.IsKnownSimple p T X P M H K :=
    ⟨hH,h.toLocalInput,h.sylow_two,h.component,h.quasisimple,hX,
      ⟨he,Or.inl ⟨hf,hmodel⟩⟩,hs.setup,hs.fitting⟩
  have hbinary : ∃ m, ChapterC.IsL2EvenBlock K m := by
    rcases ChapterC.C27Source.source_rankOne_blocks_of_sylow hs hSylow with hx | hx
    · exact hx
    · exact (hc.not_alternatingFiveBlock hp hf hmodel hx).elim
  exact ⟨h.toLocalInput,h.sylow_two,h.component,h.quasisimple,he,hf,hmodel,hX,
    hs.normalizes,hb,hbinary⟩

/-- The literal component selected for pushing up is a binary natural block
in its binary quotient branch. No block or Sylow conclusion is assumed. -/
theorem PushingUpComponent.binaryBlockEmbedding_of_binary_model
    {p : ℕ} {T X P M H K : Subgroup G}
    (h : PushingUpComponent KnownSimple.IsKnownSimple p T X P M H K)
    (hp : 3 < p) (hs : SwappedFactors T P K)
    (hmodel : SwappedModel p (XiQuotient K))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL (XiQuotient K) 2 (2^n)) :
    BinaryBlockEmbedding p T X P H K :=
  binary_swapped_block_of_pushingUp_setup
    (candidate_swapped_input h.toComponentCandidate hs hmodel) h.overgroup hp
    (FullSieve.SourceInterface.input_of_pushingUpComponent h) hn hm

/-- The literal even-field alternative in the original swapped-model list
requires no additional parameter bound. -/
theorem PushingUpComponent.binaryBlockEmbedding_of_even_swapped
    {p : ℕ} {T X P M H K : Subgroup G}
    (h : PushingUpComponent KnownSimple.IsKnownSimple p T X P M H K)
    (hp : 3 < p) (hs : SwappedFactors T P K)
    (hm : ∃ n : ℕ, Even n ∧ Nat.ModEq p (2^n) 1 ∧
      ClassicalGroup.IsPSL (XiQuotient K) 2 (2^n)) :
    BinaryBlockEmbedding p T X P H K := by
  obtain ⟨n,hn,hmod,hmodel⟩ := hm
  have hn0 : n ≠ 0 := by
    intro hn0
    obtain ⟨F,_,_,hF,_⟩ := hmodel
    have hcard := Finite.one_lt_card (α := F)
    rw [hn0,pow_zero] at hF
    omega
  have hn2 : 2 ≤ n := by obtain ⟨k,hk⟩ := hn; omega
  exact h.binaryBlockEmbedding_of_binary_model hp hs
    (Or.inl ⟨n,hn,hmod,hmodel⟩) hn2 hmodel

/-- The original binary swapped branch contradicts the irreducible odd
normalizer action once the source characteristic-control setup is supplied. -/
theorem PushingUpComponent.false_of_even_swapped
    (T : Sylow 2 G) {p : ℕ} {X P L M H K : Subgroup G}
    (h : PushingUpComponent KnownSimple.IsKnownSimple p T X P M H K)
    (hc : Configuration p T X P L M)
    (h114 : HOver G (T : Set G) ⊆ He G)
    (hs : SwappedFactors T P K)
    (hm : ∃ n : ℕ, Even n ∧ Nat.ModEq p (2^n) 1 ∧
      ClassicalGroup.IsPSL (XiQuotient K) 2 (2^n)) : False :=
  (h.binaryBlockEmbedding_of_even_swapped hc.large hs hm).false_of_centerless_factors
    T hc h.overgroup h114

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
