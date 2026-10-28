module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowOmegaGeometry
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerAlternatingGeometry
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationPrefix
public import Theory.GroupTheory.ElementaryThompsonRelative
public import CFSG.Quasithin.ChapterB.QuasisimpleOffenderModels
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Source
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.GroupTheory.SylowCentralizerComplement
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.ConjugateSpanSupplement
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan

/-!
# The actual A₇ omega-span bound

Let Z = Ω₁Z(T), W = ⟨Zᴸ⟩ and H = LT. We identify the embedded normal
closure used by `blockOmegaModule` with this literal W. The nonzero marked
weight-two vector and natural irreducibility put the original chosen V in W.
Consequently C_T(W) = O₂(H), and characteristic-normalizer control forces
Thompson movement on W and hence on the reduced module R₂(H).

Complete B.5.1 applies to that actual reduced-module action. The component's
central quotient is A₇; its order excludes the three reducible module rows.
The moved module is therefore Irr⁺, so inclusion of the original chosen
Irr⁺ member identifies it with V. In particular [W,L] = V. Sylow-fixed
coset lifting now gives Z = (V ∩ Z) C_Z(L). The natural A₇ Sylow geometry
bounds |V ∩ Z| by four, yielding |Z| ≤ 4|C_Z(L)|.

The final theorem supplies this proved bound to the literal marked-transport
consumer. It retains the allowed earlier Structural1222 input and, only for
that consumer, the independent local-model and ambient-residual inputs.
Their final discharge remains with the A₇ local-analysis assembly.

Source: Aschbacher–Smith, 3.3.6–8, 3.3.17 and 3.3.22, printed pp.587–588,
591 and 597–598, `refs/quasithin.pdf`; application to 12.3.5, printed p.809.
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
private theorem binary_linear_card (n : ℕ) :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) =
      ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
  let e := MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective,
      BinaryLinear.OuterCyclic.binary_toGL_surjective n⟩
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  rfl

private theorem not_binary_linear_central_card
    {K : Type*} [Group K] [IsQuasisimple K] [Nontrivial K]
    (hc : Nat.card (K ⧸ center K) = 2520)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : K ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : False := by
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := e.injective.nontrivial
  have he := Nat.card_congr (IsQuasisimple.centralQuotientEquiv
    e.toMonoidHom e.surjective).toEquiv
  rw [hc, BinaryLinear.OuterCyclic.binary_center_eq_bot
    (by rcases hn with rfl | rfl <;> decide),
    Nat.card_congr (QuotientGroup.quotientBot).toEquiv, binary_linear_card] at he
  rcases hn with rfl | rfl <;> norm_num [Fin.prod_univ_succ] at he

private theorem not_linear_three_central_card
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

private theorem omegaSpan_moved_irrPlus
    {D X : Type*} [Group D] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) D X) (K : Subgroup D) [IsQuasisimple K] [Nontrivial K]
    (hc : Nat.card (K ⧸ center K) = 2520)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K) :
    IsIrrPlus ρ K c.sectionData.space.toSubmodule := by
  cases c.clause_one with
  | irreducible hi _ _ _ _ => exact hi
  | doubleThree F _ e _ _ =>
    exact (not_linear_three_central_card hc F e.groupEquiv).elim
  | naturalDual n hn _ e =>
    exact (not_binary_linear_central_card hc hn (Classical.choice e).groupEquiv).elim
  | repeatedNatural n _ hn _ _ _ e =>
    exact (not_binary_linear_central_card hc hn (Classical.choice e).groupEquiv).elim

namespace SylowNormalizer.Points
variable (P : Points E)

include S in
/-- The embedded LT-normal closure is exactly the source L-conjugate span. -/
theorem omegaSpan_eq_conjugateSpan :
    blockOmegaModule T L = conjugateSpanBy (omegaCenterIn (T : Subgroup G)) L := by
  let H := L ⊔ (T : Subgroup G)
  let R : Sylow 2 H := T.subtype le_sup_right
  let Z := omegaCenterIn (T : Subgroup G)
  have hZT : Z ≤ (T : Subgroup G) :=
    fun _ hz => ((mem_omegaCenterIn_iff _ _).mp hz).1
  have hZH : Z ≤ H := hZT.trans le_sup_right
  have he : (Stellmacher.omegaOneCenterAmbient (R : Subgroup H)).map H.subtype = Z := by
    rw [← Stellmacher.omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]
    rfl
  have he' : Stellmacher.omegaOneCenterAmbient (R : Subgroup H) = Z.subgroupOf H := by
    rw [← he]
    ext x
    change x ∈ Stellmacher.omegaOneCenterAmbient (R : Subgroup H) ↔
      ∃ y : H, y ∈ Stellmacher.omegaOneCenterAmbient (R : Subgroup H) ∧
        H.subtype y = (x : G)
    constructor
    · exact fun hx => ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact H.subtype_injective hyx ▸ hy
  change (normalClosure (Stellmacher.omegaOneCenterAmbient (R : Subgroup H) : Set H)).map
    H.subtype = _
  rw [he', normalClosure_subgroupOf_eq_conjugateSpanBy Z H hZH,
    map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hZH)]
  exact conjugateSpanBy_sup_of_normalizes_seed Z L (T : Subgroup G)
    ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_omegaCenterIn _))
    S.chosen.sylow_normalizes_component

include P in
/-- The original natural chosen module lies in the actual omega span. -/
theorem chosen_le_omegaSpan : V ≤ blockOmegaModule T L := by
  let j : Multiplicative (BinaryPermutation.natural (Fin 7)) →* G :=
    V.subtype.comp (E.coordinates.symm.toMonoidHom.comp
      evenWordsEquivNatural.symm.toAddEquiv.toMultiplicative.toMonoidHom)
  have hj (v : V) : j (Multiplicative.ofAdd
      (evenWordsEquivNatural (E.coordinates v).toAdd)) = (v : G) := by
    change (E.coordinates.symm (Multiplicative.ofAdd
      (evenWordsEquivNatural.symm (evenWordsEquivNatural (E.coordinates v).toAdd))) : G) = v
    rw [evenWordsEquivNatural.symm_apply_apply, ofAdd_toAdd, E.coordinates.symm_apply_apply]
  let A : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 7)) :=
    AddSubgroup.toZModSubmodule 2 ((blockOmegaModule T L).comap j).toAddSubgroup'
  let U : Subrepresentation
      (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 7)) :=
    { toSubmodule := A
      apply_mem_toSubmodule := by
        intro a x hx
        obtain ⟨l, rfl⟩ := S.projection_surjective a
        change j (Multiplicative.ofAdd
          (BinaryPermutation.naturalRepresentation (Fin 7) (S.projection l).val x)) ∈ blockOmegaModule T L
        let v := E.coordinates.symm (Multiplicative.ofAdd (evenWordsEquivNatural.symm x))
        have he := congrArg evenWordsEquivNatural (E.equivariant l v)
        rw [evenWordsEquivNatural_equivariant] at he
        simp only [v, E.coordinates.apply_symm_apply, toAdd_ofAdd,
          evenWordsEquivNatural.apply_symm_apply] at he
        have he' : j (Multiplicative.ofAdd
            (BinaryPermutation.naturalRepresentation (Fin 7) (S.projection l).val x)) =
            (l : G) * j (Multiplicative.ofAdd x) * (l : G)⁻¹ := by
          rw [← he]
          rw [hj]
          rfl
        rw [he']
        exact (mem_normalizer_iff.mp
          (join_normalizes_blockOmegaModule (mem_sup_left l.property)) _).mp hx }
  let := BinaryPermutation.alternatingNatural_isIrreducible (Ω := Fin 7) (by simp)
  have htop : U = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left (by
    intro hbot
    let x := evenWordsEquivNatural (E.coordinates P.two).toAdd
    have hx : x ∈ U.toSubmodule := by
      change j (Multiplicative.ofAdd x) ∈ blockOmegaModule T L
      dsimp only [x]
      rw [hj]
      exact omegaCenter_le_blockOmegaModule P.two_mem_omega
    rw [hbot] at hx
    have hz : (E.coordinates P.two).toAdd = 0 :=
      evenWordsEquivNatural.injective (hx.trans evenWordsEquivNatural.map_zero.symm)
    have hp : P.two = 1 := E.coordinates.injective (by
      apply Multiplicative.toAdd.injective
      simpa only [map_one, toAdd_one] using hz)
    exact P.two_ne_one (congrArg Subtype.val hp))
  intro v hv
  have hx : evenWordsEquivNatural (E.coordinates ⟨v,hv⟩).toAdd ∈ U.toSubmodule := by
    rw [htop]
    exact Submodule.mem_top
  change j (Multiplicative.ofAdd
    (evenWordsEquivNatural (E.coordinates ⟨v,hv⟩).toAdd)) ∈ blockOmegaModule T L at hx
  rw [hj] at hx
  exact hx

include P in
/-- The actual omega span has Sylow centralizer O₂(LT). -/
theorem omegaSpan_sylow_centralizer
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) :
    (T : Subgroup G) ⊓ centralizer (blockOmegaModule T L : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  apply le_antisymm
  · exact (inf_le_inf_left _ (centralizer_le P.chosen_le_omegaSpan)).trans
      (RecognitionSource.chosen_sylow_centralizer_eq_core S.hypothesis S.chosen structural).le
  · apply le_inf ?_ (local_core_centralizes_blockOmegaModule S.hypothesis)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

include P in
/-- Escape forces the elementary Thompson subgroup to move the actual omega span. -/
theorem omegaSpan_thompson_movement
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (blockOmegaModule T L : Set G) := by
  intro hc
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hJT : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hJQ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ Q :=
    (le_inf hJT hc).trans (P.omegaSpan_sylow_centralizer structural).le
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
private theorem reduced_action_comp :
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
/-- Complete B.5.1 identifies the moved reduced module with the original chosen member. -/
theorem reduced_moved_eq_chosen
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    apply P.omegaSpan_thompson_movement structural hescape
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
  have hi := omegaSpan_moved_irrPlus _ _ hcard' c
  have hcomp : σ.comp q = ρ := reduced_action_comp (T := T) (L := L)
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
/-- The moved part of the actual omega span is the original natural module. -/
theorem omegaSpan_commutator_eq_chosen
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    rw [← P.reduced_moved_eq_chosen structural hescape]
    exact Submodule.subset_span ⟨l',hl,v,Submodule.mem_top,rfl⟩
  rw [← S.chosen.image_eq]
  have hm' : (reducedRepresentation H l' v - v).toMul ∈
      S.chosen.space.toAddSubgroup.toSubgroup' := hm
  have hmG := mem_map_of_mem H.subtype (mem_map_of_mem (ReducedModule H).subtype hm')
  change l * (r : G) * l⁻¹ / (r : G) ∈ subspaceImage H S.chosen.space at hmG
  simpa only [commutatorElement_def, div_eq_mul_inv, Subgroup.subtype_apply, H] using hmG

private def sylowPairA : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 5 6, by change Equiv.Perm.sign _ = 1; decide⟩
private def sylowPairB : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by change Equiv.Perm.sign _ = 1; decide⟩

private def sylowPairC : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by change Equiv.Perm.sign _ = 1; decide⟩

private def sylowEntry : Fin 8 → alternatingGroup (Fin 7) :=
  ![1,sylowPairC,sylowPairB,sylowPairC*sylowPairB,sylowPairA,
    sylowPairC*sylowPairA,sylowPairB*sylowPairA,sylowPairC*sylowPairB*sylowPairA]

private def sylowGroup : Subgroup (alternatingGroup (Fin 7)) where
  carrier := Set.range sylowEntry
  one_mem' := ⟨0,rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩
    exact (by decide +kernel : ∀ i j : Fin 8, ∃ k,
      sylowEntry k = sylowEntry i * sylowEntry j) i j
  inv_mem' := by
    rintro _ ⟨i,rfl⟩
    exact (by decide +kernel : ∀ i : Fin 8, ∃ j,
      sylowEntry j = (sylowEntry i)⁻¹) i

private theorem sylowGroup_card : Nat.card sylowGroup = 8 := by
  change Nat.card (Set.range sylowEntry) = 8
  rw [Nat.card_congr (Equiv.ofInjective sylowEntry (by decide +kernel)).symm]
  exact Nat.card_fin 8

private noncomputable def standardSylow : Sylow 2 (alternatingGroup (Fin 7)) :=
  Sylow.ofCard sylowGroup (by
    rw [sylowGroup_card,nat_card_alternatingGroup,Nat.card_fin]
    decide +kernel)

private theorem sylowPair_mem : sylowPairA ∈ standardSylow ∧ sylowPairB ∈ standardSylow :=
  ⟨⟨4,rfl⟩,⟨2,rfl⟩⟩

private theorem fixed_pair_coordinates (v : EvenWord)
    (ha : evenRepresentation sylowPairA.val v = v)
    (hb : evenRepresentation sylowPairB.val v = v) :
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
private theorem exists_component_sylow :
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

include E in
/-- A Sylow of the actual component fixes at most four points of the natural module. -/
theorem natural_omega_card_le_four :
    Nat.card (V ⊓ omegaCenterIn (T : Subgroup G) : Subgroup G) ≤ 4 := by
  obtain ⟨R,hR⟩ := exists_component_sylow (S := S)
  let U := R.mapSurjective S.projection_surjective
  let U₀ := standardSylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) U₀ U
  have he : (U₀ : Subgroup (alternatingGroup (Fin 7))).map
      (MulAut.conj g).toMonoidHom = U := by
    change ((g • U₀ : Sylow 2 (alternatingGroup (Fin 7))) : Subgroup (alternatingGroup (Fin 7))) = _
    rw [hg]
  let D := V ⊓ omegaCenterIn (T : Subgroup G)
  let f : D → EvenWord := fun v => evenRepresentation g⁻¹.val
    (E.coordinates ⟨v,v.property.1⟩).toAdd
  have hfix (v : D) (a : alternatingGroup (Fin 7)) (ha : a ∈ U₀) :
      evenRepresentation a.val (f v) = f v := by
    have hmem : g*a*g⁻¹ ∈ (U : Subgroup (alternatingGroup (Fin 7))) := by
      rw [← he]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom ha
    obtain ⟨l,hl,heq⟩ := hmem
    have hv := E.equivariant l (⟨v,v.property.1⟩ : V)
    have hcomm := ((mem_omegaCenterIn_iff _ _).mp v.property.2).2.1 l (hR l hl)
    have hact : V.normalizerMonoidHom ⟨l,S.chosen.normalizes l.property⟩
        ⟨v,v.property.1⟩ = ⟨v,v.property.1⟩ := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr hcomm
    rw [hact,heq] at hv
    have hh := congrArg (evenRepresentation g⁻¹.val) hv.symm
    have hmul : (g⁻¹ * (g*a*g⁻¹)).val = (a*g⁻¹).val := by congr 1; group
    simpa only [f, ← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, hmul] using hh
  let pair : D → ZMod 2 × ZMod 2 := fun v => ((f v).val 0,(f v).val 5)
  have hi : Function.Injective pair := by
    intro v w h
    have h0 := congrArg Prod.fst h
    have h5 := congrArg Prod.snd h
    have hv := fixed_pair_coordinates (f v) (hfix v _ sylowPair_mem.1)
      (hfix v _ sylowPair_mem.2)
    have hw := fixed_pair_coordinates (f w) (hfix w _ sylowPair_mem.1)
      (hfix w _ sylowPair_mem.2)
    have heq : f v = f w := by
      apply Subtype.ext
      rw [hv,hw]
      change (f v).val 0 = (f w).val 0 at h0
      change (f v).val 5 = (f w).val 5 at h5
      rw [h0,h5]
    have hvec : (E.coordinates ⟨v,v.property.1⟩).toAdd =
        (E.coordinates ⟨w,w.property.1⟩).toAdd :=
      (LinearMap.GeneralLinearGroup.toLinearEquiv (evenRepresentation.asGroupHom g⁻¹.val)).injective heq
    have hV := E.coordinates.injective (Multiplicative.toAdd.injective hvec)
    exact Subtype.ext (congrArg (fun x : V => (x : G)) hV)
  have hc := Nat.card_le_card_of_injective pair hi
  simpa only [Nat.card_prod, Nat.card_zmod] using hc

/-- Sylow-fixed coset lifting supplies the actual central supplement in Ω₁Z(T). -/
theorem omega_splitting
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    omegaCenterIn (T : Subgroup G) = (V ⊓ omegaCenterIn (T : Subgroup G)) ⊔ P.fixed := by
  let := S.chosen.elementary
  let H := L ⊔ (T : Subgroup G)
  let Z := omegaCenterIn (T : Subgroup G)
  have hTV := ((structural G T L S.hypothesis).2.2 V S.chosen).1
  have hHV : H ≤ normalizer (V : Set G) := sup_le S.chosen.normalizes hTV
  have hLZ : ⁅L,Z⁆ ≤ V := by
    rw [commutator_comm]
    exact (commutator_mono omegaCenter_le_blockOmegaModule le_rfl).trans
      (P.omegaSpan_commutator_eq_chosen structural hescape).le
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

/-- The omega-center bound consumed by the hyperplane argument in source 3.3.22. -/
theorem omega_card_bound
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
  have hs := P.omega_splitting structural hescape
  have hbound := natural_omega_card_le_four (E := E)
  change Nat.card A ≤ 4 at hbound
  rw [← hs] at hc
  calc
    Nat.card Z ≤ Nat.card A * Nat.card P.fixed := by nlinarith
    _ ≤ _ := Nat.mul_le_mul_right _ hbound

/-- Discharge the omega-cardinality premise of the literal marked-transport consumer. -/
theorem transport_of_omegaSpan
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (M : P.Models) (R : P.AmbientResiduals)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ g ∈ normalizer (T : Set G), g * (P.two : G) * g⁻¹ = P.six :=
  P.transport_of_omega_card_bound M R hescape (P.omega_card_bound structural hescape)

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
