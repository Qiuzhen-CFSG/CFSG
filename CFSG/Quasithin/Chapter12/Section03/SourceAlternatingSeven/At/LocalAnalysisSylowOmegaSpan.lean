module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAt.Basic
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowOmegaSpan
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowReduction

/-!
# LocalAnalysisSylowOmegaSpan at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisSylowOmegaSpan`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open scoped commutatorElement

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

open Section02.RecognitionSource.FusionReducibleNormalizer

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

open ChapterB.QuasisimpleSource

private theorem binary_linear_card_at (n : ℕ) :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) =
      ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
  let e := MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective,
      BinaryLinear.OuterCyclic.binary_toGL_surjective n⟩
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  rfl

private theorem not_binary_linear_central_card_at
    {K : Type*} [Group K] [IsQuasisimple K] [Nontrivial K]
    (hc : Nat.card (K ⧸ center K) = 2520)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : K ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : False := by
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := e.injective.nontrivial
  have he := Nat.card_congr (IsQuasisimple.centralQuotientEquiv
    e.toMonoidHom e.surjective).toEquiv
  rw [hc, BinaryLinear.OuterCyclic.binary_center_eq_bot
    (by rcases hn with rfl | rfl <;> decide),
    Nat.card_congr (QuotientGroup.quotientBot).toEquiv, binary_linear_card_at] at he
  rcases hn with rfl | rfl <;> norm_num [Fin.prod_univ_succ] at he

private theorem not_linear_three_central_card_at
    {K : Type*} [Group K] [IsQuasisimple K] [Nontrivial K]
    (hc : Nat.card (K ⧸ center K) = 2520)
    (F : BinaryField) (e : K ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) : False := by
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) := e.injective.nontrivial
  have he := Nat.card_congr (IsQuasisimple.centralQuotientEquiv
    e.toMonoidHom e.surjective).toEquiv
  have hcard : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F.Carrier) = 2520 :=
    he.symm.trans hc
  have h := Matrix.PSL3.LinearThree.card_projective_mul_scalar F.Carrier
  rw [hcard] at h
  by_cases hd : F.degree = 1
  · norm_num [F.card_eq, hd] at h
  · have hq : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact Nat.pow_le_pow_right (n := 2) (by decide) (i := 2) (by have := F.degree_pos; omega)
    have hg := Nat.gcd_le_left (Nat.card F.Carrier - 1) (by decide : 0 < 3)
    have hbig : 60480 ≤ Nat.card F.Carrier ^ 3 *
        (Nat.card F.Carrier ^ 3 - 1) * (Nat.card F.Carrier ^ 2 - 1) := by
      calc
        60480 = 4 ^ 3 * (4 ^ 3 - 1) * (4 ^ 2 - 1) := by norm_num
        _ ≤ _ := by gcongr
    omega

private theorem omegaSpan_moved_irrPlus_at
    {D X : Type*} [Group D] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) D X) (K : Subgroup D) [IsQuasisimple K] [Nontrivial K]
    (hc : Nat.card (K ⧸ center K) = 2520)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K) :
    IsIrrPlus ρ K c.sectionData.space.toSubmodule := by
  cases c.clause_one with
  | irreducible hi _ _ _ _ => exact hi
  | doubleThree F _ e _ _ =>
    exact (not_linear_three_central_card_at hc F e.groupEquiv).elim
  | naturalDual n hn _ e =>
    exact (not_binary_linear_central_card_at hc hn (Classical.choice e).groupEquiv).elim
  | repeatedNatural n _ hn _ _ _ e =>
    exact (not_binary_linear_central_card_at hc hn (Classical.choice e).groupEquiv).elim

namespace SylowNormalizer.Points

variable (P : Points E)

include P in

theorem omegaSpan_sylow_centralizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    (T : Subgroup G) ⊓ centralizer (blockOmegaModule T L : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  apply le_antisymm
  · exact (inf_le_inf_left _ (centralizer_le P.chosen_le_omegaSpan)).trans
      (RecognitionSource.chosen_sylow_centralizer_eq_core_at S.hypothesis S.chosen structural).le
  · apply le_inf ?_ (local_core_centralizes_blockOmegaModule S.hypothesis)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

include P in

theorem omegaSpan_thompson_movement_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (blockOmegaModule T L : Set G) := by
  intro hc
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hJT : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hJQ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ Q :=
    (le_inf hJT hc).trans (P.omegaSpan_sylow_centralizer_at structural).le
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have he := Stellmacher.elementaryAbelianMaxJ_eq_of_intermediate_finite
    (T : Subgroup G) Q hJQ hQT
  have hne : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≠ ⊥ :=
    Stellmacher.elementaryAbelianMaxJ_ne_bot_of_finite_pGroup _ T.isPGroup'
      (fun h => S.chosen.ne_bot (bot_unique (S.chosen.le_sylow.trans_eq h)))
  have hnorm : L ⊔ (T : Subgroup G) ≤ normalizer
      (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    rw [← he]
    exact ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))).trans
        (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ Q)
  exact hescape ((Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ _).trans
    (S.chosen.normal_subgroup_normalizer_le S.hypothesis.toHypothesis1221
      (hJT.trans le_sup_right) hne hnorm))

open Representation Representation.BinaryOffender Stellmacher

open ChapterB.InternalThompsonAction

omit [Finite G] in

private theorem reduced_action_comp_at :
    (action (ReducedModule (L ⊔ (T : Subgroup G)))).comp
      (actionMk (ReducedModule (L ⊔ (T : Subgroup G)))) =
        reducedRepresentation (L ⊔ (T : Subgroup G)) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  apply Additive.toMul.injective
  apply Subtype.ext
  exact action_apply _ g v

include P in

theorem reduced_moved_eq_chosen_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    subspaceCommutator (reducedRepresentation (L ⊔ (T : Subgroup G))) ⊤
      (L.subgroupOf (L ⊔ (T : Subgroup G))) = S.chosen.space := by
  let H := L ⊔ (T : Subgroup G)
  let W := ReducedModule H
  let K := L.subgroupOf H
  let R : Sylow 2 H := T.subtype le_sup_right
  let q := actionMk W
  let σ := action W
  let ρ := reducedRepresentation H
  let B := K.map q
  let J := offenderSubgroup σ
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer S.chosen.sylow_normalizes_component)
  have hKP : K ⊔ (R : Subgroup H) = ⊤ := by
    change L.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hcore : pCore 2 (ActionQuotient W) = ⊥ :=
    isPReduced_reducedPSubgroup.quotient_pCore_eq_bot
  have hmove : ¬ elementaryAbelianMaxJ (R : Subgroup H) ≤ centralizer (W : Set H) := by
    intro hc
    apply P.omegaSpan_thompson_movement_at structural hescape
    have hj : (elementaryAbelianMaxJ (R : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
      congr 1
      exact map_subgroupOf_eq_of_le le_sup_right
    have hWR : blockOmegaModule T L ≤ W.map H.subtype :=
      map_mono ((omegaCenter_normalClosure_reduced R
        (RecognitionSource.FusionReducibleNormalizer.join_characteristicTwo S.hypothesis)).le_reducedPSubgroup)
    rw [← hj]
    rintro _ ⟨a,ha,rfl⟩ z hz
    obtain ⟨w,hw,rfl⟩ := hWR hz
    exact congrArg H.subtype (hc ha w hw)
  have hK : K.IsCComponent := S.hypothesis.maximal_faithful.1.1.1
  let : IsQuasisimple B := quasisimple_of_thompson_movement
    ChapterB.SourceInduction.adequateClassification_knownSimple
    S.hypothesis.toHypothesis1221.join_sqtk R K W hK hKP hcore hmove
  let : IsSimpleGroup (B ⧸ center B) := (inferInstance : IsQuasisimple B).simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  have hBJ : B ≤ J := component_le_offenderSubgroup R K W hKP hcore hmove
  obtain ⟨c⟩ := quasisimple_source_conclusion_of_thompson_movement
    S.hypothesis.toHypothesis1221.join_sqtk R K W hK hKP hcore hmove
  let f : L →* B := (q.subgroupMap K).comp (subgroupOfEquivOfLe
    (show L ≤ H from le_sup_left)).symm.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective K).comp
    (subgroupOfEquivOfLe le_sup_left).symm.surjective
  have hk : pCore 2 L ≤ f.ker := by
    have hp : L.pCoreIn 2 ≤ H.pCoreIn 2 := pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer S.chosen.sylow_normalizes_component)
    intro l hl
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨r,hr,he⟩ := hp (mem_map_of_mem L.subtype hl)
    have he' : r = (⟨l,mem_sup_left l.property⟩ : H) := Subtype.ext he
    rw [he'] at hr
    exact (le_centralizer_iff.mp (reducedPSubgroup_le_centralizer_pCore 2 H)) hr
  let f' : (L ⧸ pCore 2 L) →* B := QuotientGroup.lift _ f hk
  have hf' : Function.Surjective f' := QuotientGroup.lift_surjective_of_surjective _ f hf hk
  let := S.hypothesis.quasisimple
  have hcard : Nat.card (B ⧸ center B) = 2520 := by
    rw [← Nat.card_congr (IsQuasisimple.centralQuotientEquiv f' hf').toEquiv]
    rw [Nat.card_congr ((centralPreimageQuotientEquiv (pCore 2 L)).symm.trans
      S.quotient).toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  let e : B.subgroupOf J ≃* B := subgroupOfEquivOfLe hBJ
  let : IsQuasisimple (B.subgroupOf J) := IsQuasisimple.of_mulEquiv e.symm
  let : Nontrivial (B.subgroupOf J) := e.surjective.nontrivial
  have hcard' : Nat.card ((B.subgroupOf J) ⧸ center (B.subgroupOf J)) = 2520 := by
    rw [Nat.card_congr (IsQuasisimple.centralQuotientEquiv e.toMonoidHom e.surjective).toEquiv]
    exact hcard
  have hi := omegaSpan_moved_irrPlus_at _ _ hcard' c
  have hcomp : σ.comp q = ρ := reduced_action_comp_at (T := T) (L := L)
  have hmoved : c.sectionData.space.toSubmodule = subspaceCommutator ρ ⊤ K := by
    rw [c.sectionData.space_eq]
    change subspaceCommutator (σ.comp J.subtype) ⊤ (B.subgroupOf J) = _
    rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hBJ]
    change subspaceCommutator σ ⊤ (K.map q) = _
    rw [← subspaceCommutator_comp_map, hcomp]
  have hirr : IsIrrPlus σ B c.sectionData.space.toSubmodule :=
    (IsIrrPlus.subgroupOf_iff σ B J hBJ _).mp hi
  have hirr' : IsIrrPlus ρ K c.sectionData.space.toSubmodule := by
    have hh := IsIrrPlus.map_embedding ρ σ q (LinearMap.id) Function.injective_id
      (fun g v => by change ρ g v = σ (q g) v; rw [← hcomp]; rfl)
      K c.sectionData.space.toSubmodule hirr
    simpa only [Submodule.map_id] using hh
  rw [hmoved] at hirr'
  apply (IsIrrPlus.eq_of_le ρ S.chosen.irrPlus.isIrrPlus hirr' _).symm
  rw [← S.chosen.irrPlus.isIrrPlus.choose_spec.1]
  exact subspaceCommutator_mono_left ρ le_top K

include P in

theorem omegaSpan_commutator_eq_chosen_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ⁅blockOmegaModule T L,L⁆ = V := by
  apply le_antisymm _
    (S.chosen.eq_commutator.le.trans (commutator_mono P.chosen_le_omegaSpan le_rfl))
  let H := L ⊔ (T : Subgroup G)
  have hWR : blockOmegaModule T L ≤ (ReducedModule H).map H.subtype :=
    map_mono ((omegaCenter_normalClosure_reduced (T.subtype le_sup_right)
      (RecognitionSource.FusionReducibleNormalizer.join_characteristicTwo S.hypothesis)).le_reducedPSubgroup)
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl w hw
  obtain ⟨r,hr,rfl⟩ := hWR hw
  let l' : H := ⟨l,mem_sup_left hl⟩
  let v : Additive (ReducedModule H) := Additive.ofMul ⟨r,hr⟩
  have hm : reducedRepresentation H l' v - v ∈ S.chosen.space := by
    rw [← P.reduced_moved_eq_chosen_at structural hescape]
    exact Submodule.subset_span ⟨l',hl,v,Submodule.mem_top,rfl⟩
  rw [← S.chosen.image_eq]
  have hm' : (reducedRepresentation H l' v - v).toMul ∈
      S.chosen.space.toAddSubgroup.toSubgroup' := hm
  have hmG := mem_map_of_mem H.subtype (mem_map_of_mem (ReducedModule H).subtype hm')
  change l * (r : G) * l⁻¹ / (r : G) ∈ subspaceImage H S.chosen.space at hmG
  simpa only [commutatorElement_def, div_eq_mul_inv, Subgroup.subtype_apply, H] using hmG

private def sylowPairA_at : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 5 6, by change Equiv.Perm.sign _ = 1; decide⟩

private def sylowPairB_at : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by change Equiv.Perm.sign _ = 1; decide⟩

private def sylowPairC_at : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by change Equiv.Perm.sign _ = 1; decide⟩

private def sylowEntry_at : Fin 8 → alternatingGroup (Fin 7) :=
  ![1,sylowPairC_at,sylowPairB_at,sylowPairC_at*sylowPairB_at,sylowPairA_at,
    sylowPairC_at*sylowPairA_at,sylowPairB_at*sylowPairA_at,sylowPairC_at*sylowPairB_at*sylowPairA_at]

private def sylowGroup_at : Subgroup (alternatingGroup (Fin 7)) where
  carrier := Set.range sylowEntry_at
  one_mem' := ⟨0,rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩
    exact (by decide +kernel : ∀ i j : Fin 8, ∃ k,
      sylowEntry_at k = sylowEntry_at i * sylowEntry_at j) i j
  inv_mem' := by
    rintro _ ⟨i,rfl⟩
    exact (by decide +kernel : ∀ i : Fin 8, ∃ j,
      sylowEntry_at j = (sylowEntry_at i)⁻¹) i

private theorem sylowGroup_card_at : Nat.card sylowGroup_at = 8 := by
  change Nat.card (Set.range sylowEntry_at) = 8
  rw [Nat.card_congr (Equiv.ofInjective sylowEntry_at (by decide +kernel)).symm]
  exact Nat.card_fin 8

private noncomputable def standardSylow_at : Sylow 2 (alternatingGroup (Fin 7)) :=
  Sylow.ofCard sylowGroup_at (by
    rw [sylowGroup_card_at,nat_card_alternatingGroup,Nat.card_fin]
    decide +kernel)

private theorem sylowPair_mem_at : sylowPairA_at ∈ standardSylow_at ∧ sylowPairB_at ∈ standardSylow_at :=
  ⟨⟨4,rfl⟩,⟨2,rfl⟩⟩

private theorem fixed_pair_coordinates_at (v : EvenWord)
    (ha : evenRepresentation sylowPairA_at.val v = v)
    (hb : evenRepresentation sylowPairB_at.val v = v) :
    v.val = ![v.val 0,v.val 0,v.val 0,v.val 0,0,v.val 5,v.val 5] := by
  have h10 := congrArg (fun w : EvenWord => w.val 0) ha
  have h65 := congrArg (fun w : EvenWord => w.val 5) ha
  have h20 := congrArg (fun w : EvenWord => w.val 0) hb
  have h31 := congrArg (fun w : EvenWord => w.val 1) hb
  change v.val 1 = v.val 0 at h10
  change v.val 6 = v.val 5 at h65
  change v.val 2 = v.val 0 at h20
  change v.val 3 = v.val 1 at h31
  have hs := (mem_evenWords_iff v.val).mp v.property
  simp only [Fin.sum_univ_succ] at hs
  change v.val 0 + (v.val 1 + (v.val 2 + (v.val 3 +
    (v.val 4 + (v.val 5 + (v.val 6 + 0)))))) = 0 at hs
  have h4 : v.val 4 = 0 := by
    rw [h31,h10,h20,h65] at hs
    have h := (by decide : ∀ a b c : ZMod 2,
      a+(a+(a+(a+(b+(c+(c+0)))))) = 0 → b=0)
    exact h _ _ _ hs
  funext i
  fin_cases i <;> simp_all

include S in

private theorem exists_component_sylow_at :
    ∃ R : Sylow 2 L, ∀ l ∈ (R : Subgroup L), (l : G) ∈ (T : Subgroup G) := by
  let H := L ⊔ (T : Subgroup G)
  let K := L.subgroupOf H
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer S.chosen.sylow_normalizes_component)
  let U : Sylow 2 H := T.subtype le_sup_right
  obtain ⟨R,hR⟩ := U.exists_subgroupOf_eq_of_normal K
  let e : K ≃* L := subgroupOfEquivOfLe (le_sup_left : L ≤ H)
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro l ⟨r,hr,rfl⟩
  rw [hR] at hr
  exact hr

theorem omega_splitting_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    omegaCenterIn (T : Subgroup G) = (V ⊓ omegaCenterIn (T : Subgroup G)) ⊔ P.fixed := by
  let := S.chosen.elementary
  let H := L ⊔ (T : Subgroup G)
  let Z := omegaCenterIn (T : Subgroup G)
  have hTV := ((structural L S.hypothesis).2.2 V S.chosen).1
  have hHV : H ≤ normalizer (V : Set G) := sup_le S.chosen.normalizes hTV
  have hLZ : ⁅L,Z⁆ ≤ V := by
    rw [commutator_comm]
    exact (commutator_mono omegaCenter_le_blockOmegaModule le_rfl).trans
      (P.omegaSpan_commutator_eq_chosen_at structural hescape).le
  have hTZ : ⁅(T : Subgroup G),Z⁆ = ⊥ := by
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz
    exact ((mem_omegaCenterIn_iff _ _).mp hz).2.1
  have hHZ : ⁅H,Z⁆ ≤ V := commutator_sup_le_of_relative_normal H L T Z V
    hHV le_sup_left le_sup_right hLZ (by rw [hTZ]; exact bot_le)
  apply le_antisymm ?_ (sup_le inf_le_right inf_le_left)
  intro z hz
  obtain ⟨v,hv,hvz⟩ := fixed_coset_of_sylow H V hHV
    (fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv)
    (T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)) z
    (fun a ha => commutator_le.mp hHZ a ha z hz)
    (fun a ha => ((mem_omegaCenterIn_iff _ _).mp hz).2.1 a ha)
  have hzT := ((mem_omegaCenterIn_iff _ _).mp hz).2.1
  have hvzT := centralizer_le (show (T : Subgroup G) ≤ H from le_sup_right) hvz
  have hvT : v ∈ centralizer (T : Set G) := by
    simpa only [mul_inv_cancel_right] using
      (centralizer (T : Set G)).mul_mem hvzT ((centralizer _).inv_mem hzT)
  have hvZ : v ∈ Z := (mem_omegaCenterIn_iff _ _).mpr
    ⟨S.chosen.le_sylow hv,hvT,elemPow_eq_one_of_isElementaryAbelian v hv⟩
  have hfix : v*z ∈ P.fixed := ⟨Z.mul_mem hvZ hz,
    centralizer_le (show L ≤ H from le_sup_left) hvz⟩
  have hm := mul_mem_sup (show v⁻¹ ∈ V ⊓ Z from ⟨V.inv_mem hv,Z.inv_mem hvZ⟩) hfix
  simpa only [inv_mul_cancel_left] using hm

theorem omega_card_bound_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    Nat.card (omegaCenterIn (T : Subgroup G)) ≤ 4 * Nat.card P.fixed := by
  let Z := omegaCenterIn (T : Subgroup G)
  let A := V ⊓ Z
  have hn : P.fixed ≤ normalizer (A : Set G) := by
    intro b hb
    apply Subgroup.centralizer_le_normalizer
    intro a ha
    exact ((mem_omegaCenterIn_iff _ _).mp hb.1).2.1 a
      ((mem_omegaCenterIn_iff _ _).mp ha.2).1
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes A P.fixed hn
  have hpos : 1 ≤ Nat.card (A ⊓ P.fixed : Subgroup G) := Nat.card_pos
  have hs := P.omega_splitting_at structural hescape
  have hbound := natural_omega_card_le_four (E := E)
  change Nat.card A ≤ 4 at hbound
  rw [← hs] at hc
  calc
    Nat.card Z ≤ Nat.card A * Nat.card P.fixed := by nlinarith
    _ ≤ _ := Nat.mul_le_mul_right _ hbound

theorem transport_of_omegaSpan_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (M : P.Models) (R : P.AmbientResiduals)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ g ∈ normalizer (T : Set G), g * (P.two : G) * g⁻¹ = P.six :=
  P.transport_of_omega_card_bound M R hescape (P.omega_card_bound_at structural hescape)

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

