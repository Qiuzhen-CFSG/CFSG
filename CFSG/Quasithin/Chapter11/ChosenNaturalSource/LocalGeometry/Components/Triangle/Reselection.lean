module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ThirdVertexRecognitionSp4
public import CFSG.Quasithin.Chapter1.Section02.Adequate.OrbitFaithful
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Selection
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankTwoPerfect
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.G2Perfect
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.TrialityPerfect
public import Theory.GroupTheory.PrimeRankResidualCentralizer

/-!
# Selecting modules and comparing maximal overcomponents at the third vertex

A normalized faithful local component with quasisimple two-core quotient
acts nontrivially on R₂(IT). A.1.42 therefore selects its actual homogeneous
Irr⁺ module. This specializes the proof in ReductionSource.Selection to
its used hypotheses, so the construction is available before maximality.

Cubic rank two forces equality with a containing local component whose
literal quotient is PSL₃(4), Sp₄(4), G₂(4), or ³D₄(4), by the native
full-Sylow overgroup calculations. For an SL₃(4) containing quotient,
the orders of the three recognized third-vertex models force equality
of the actual images. Equality is lifted through the original two-core.

The faithful maximal envelope preserves normalization, quasisimplicity,
the same ambient Hypothesis 12.2.3 and a literal chosen module. The next
module applies these results to I = K₀ ∨ L₂, reducing any strict envelope
to the exceptional field-four rows. Identifying I with its envelope and
proving the reselected action natural remain with
qt-d-1222-natural-relative-components, as do common-normal existence,
the source SL₃(4) exclusion and both triangle orientations.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
11.1.2, printed pp.762--764; A.1.42, A.4.11 and 1.2.8--9, pp.32,61,506--507.
-/

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
open Chapter1.Section02 Chapter1.Section02.Adequate
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem central_two_chief_of_quasisimple
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q] :
    HasCentralPChiefFactors 2 Q := by
  let e : (Q ⧸ (⊥ : Subgroup Q)) ≃* Q := QuotientGroup.quotientBot
  let : IsQuasisimple (Q ⧸ (⊥ : Subgroup Q)) :=
    IsQuasisimple.of_mulEquiv e.symm
  exact hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
    (⊥ : Subgroup Q) (by simp) inferInstance

/-- The same L acts nontrivially on the actual R₂(LT). -/
private theorem faithful_reduced_commutator_ne_bot
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (hn : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ⁅reducedTwoSubgroup (L ⊔ (T : Subgroup G) : Subgroup G),
      L.subgroupOf (L ⊔ (T : Subgroup G))⁆ ≠ ⊥ := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hn)
  let e : A ≃* L := subgroupOfEquivOfLe le_sup_left
  have hp : IsPPerfect 2 A :=
    hf.1.2.1.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hmap : A.map H.subtype = L := map_subgroupOf_eq_of_le le_sup_left
  have hne : ChapterA.Section04.intrinsicSignalizerModule A ≠ ⊥ := by
    intro he
    apply hf.2
    rw [← hmap, ChapterA.Section04.intrinsicSignalizerModule_map_of_injective
      H.subtype H.subtype_injective, he, Subgroup.map_bot]
  let eQ := QuotientGroup.congr (pCore 2 A) (pCore 2 L) e (pCore_map_iso 2 e)
  let := hq
  let : IsQuasisimple (A ⧸ pCore 2 A) :=
    IsQuasisimple.of_mulEquiv eQ.symm
  have hc : HasCentralPChiefFactorsAbove 2 (pCore 2 A) :=
    (hasCentralPChiefFactorsAbove_iff_quotient _).mpr central_two_chief_of_quasisimple
  exact ChapterA.Section04.reduced_commutator_ne_bot_of_intrinsicModule_ne_bot A
    (show A.Normal from inferInstance).isSubnormal hp hc hne

/-- The original hypotheses and already available normalization construct a
homogeneous chosen module on the literal reduced subgroup. -/
theorem exists_chosen_of_normalized_faithful
    (hL : L ∈ Chapter1.L G T)
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (hn : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ V : Subgroup G, Nonempty (ChosenModule T L V) := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hn)
  let e : A ≃* L := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect hL
  let : Group.IsPerfect A :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hnot : ¬ (⊤ : Submodule (ZMod 2) (Additive (ReducedModule H))) ≤
      fixedSpace (reducedRepresentation H) A := by
    intro hfixed
    apply faithful_reduced_commutator_ne_bot hf hq hn
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro v hv x hx
    have hh := congrArg (fun w : Additive (ReducedModule H) => w.toMul.val)
      (hfixed (show Additive.ofMul (⟨v, hv⟩ : ReducedModule H) ∈ ⊤ from trivial) ⟨x, hx⟩)
    change x * v * x⁻¹ = v at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨I, hI⟩ := exists_isIrrPlus_of_not_fixed (reducedRepresentation H) A hnot
  have hT : (T : Subgroup G).subgroupOf H ≤ normalizer (A : Set H) :=
    le_normalizer_of_normal
  obtain ⟨J, _, hJ⟩ := exists_isIrrPlusWith_le_orbitSpan (reducedRepresentation H)
    hT T.isPGroup'.comap_subtype hI
  exact ⟨subspaceImage H J, ⟨⟨J, hJ, rfl⟩⟩⟩

/-- A cubic-rank-two local component exhausts any containing component
whose original two-core quotient is PSL₃(4), Sp₄(4), G₂(4), or ³D₄(4). Equality
is lifted through the original ambient two-core and the same full Sylow. -/
theorem local_eq_of_field_four_rank_two_overgroup
    {I J : Subgroup G} (hI : I ∈ Chapter1.L G T) (hJ : J ∈ Chapter1.L G T)
    (hIJ : I ≤ J) (hr : 2 ≤ primeRank 3 I)
    (hm : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 4 ∨
      Source.IsSp (J ⧸ pCore 2 J) 2 4 ∨
      ClassificationModels.IsG2At (J ⧸ pCore 2 J) 4 ∨
      Triality.Standard.IsTrialityGroupAt 4 (J ⧸ pCore 2 J)) : I = J := by
  let H := J ⊔ (T : Subgroup G)
  have hIH : I ≤ H := hIJ.trans le_sup_left
  let P := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hb : I.subgroupOf H ∈ Chapter1.L H (P : Subgroup H) :=
    (Chapter1.mem_LIn_iff_subgroupOf le_sup_right hIH).mp ⟨hIH,hI⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  let j := subgroupOfEquivOfLe (show J ≤ H from le_sup_left)
  let jq := QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
  let e : (J.subgroupOf H).map q ≃* (J ⧸ pCore 2 J) :=
    (cComponentTwoCoreQuotientEquiv hJ.1).symm.trans jq
  have hrb : 2 ≤ primeRank 3 ((I.subgroupOf H).map q) := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3) q
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup),
      primeRank_congr 3 (subgroupOfEquivOfLe hIH)]
    exact hr
  have he : (I.subgroupOf H).map q = (J.subgroupOf H).map q := by
    rcases hm with hm | hm | hm | hm
    · obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hm
      let := hF
      let := hfin
      let := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
        (by simpa [←Nat.card_eq_fintype_card] using hcard)
      exact ChapterA.Section03.SourceEmbeddings.twoCore_images_eq_of_linear_three_containing_component
        P hb hJ.1 (comap_mono hIJ) (by decide : Odd 3) hrb
        (by decide : 1 < 2) hcard (e.trans a)
    · obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hm
      let := hF
      let := hfin
      let := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
        (by simpa [←Nat.card_eq_fintype_card] using hcard)
      exact ChapterA.Section03.SourceEmbeddings.twoCore_images_eq_of_symplectic_four_containing_component
        P hb hJ.1 (comap_mono hIJ) (by decide : Odd 3) hrb
        (by omega) (e.trans a)
    · obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hm
      let := hF
      let := hfin
      let := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
        (by simpa [←Nat.card_eq_fintype_card] using hcard)
      let := pCore_isNilpotent (p := 2) (G := H)
      exact ChapterA.Section03.SourceEmbeddings.eq_of_g2_containing_component_of_odd_rank
        (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)))
        (mem_L_map_twoCore_mem_localCComponents hb) (hJ.1.map_quotient _)
        (map_mono (comap_mono hIJ)) (by decide : Odd 3) hrb (by omega) (e.trans a)
    · obtain ⟨a⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ 2 (by decide)).mp hm
      let := pCore_isNilpotent (p := 2) (G := H)
      exact ChapterA.Section03.SourceEmbeddings.eq_of_triality_containing_component_of_odd_rank
        (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)))
        (mem_L_map_twoCore_mem_localCComponents hb) (hJ.1.map_quotient _)
        (map_mono (comap_mono hIJ)) (by decide : Odd 3) hrb (by decide : 0 < 2) (e.trans a)
  have hij := MovedMaximality.eq_of_twoCore_images_eq P hb.1 hJ.1 (comap_mono hIJ) he
  change I.subgroupOf H = J.subgroupOf H at hij
  simpa only [map_subgroupOf_eq_of_le hIH,map_subgroupOf_eq_of_le (show J ≤ H from le_sup_left)]
    using congrArg (map H.subtype) hij

private theorem sl_three_four_card {A : Type*} [Group A]
    (hm : Source.IsSL A 3 4) : Nat.card A = 60480 := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  rw [Nat.card_congr e.toEquiv,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (center (Matrix.SpecialLinearGroup (Fin 3) F)),
    Atlas.ExceptionalSupport.card_sl_center]
  change Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) * _ = _
  rw [Matrix.PSL3.LinearThree.card_projective,hcard]
  norm_num

private theorem triangle_card_lower {A : Type*} [Group A]
    (hm : Source.IsSL A 3 4 ∨ Source.IsSp A 2 4 ∨ ClassificationModels.IsG2At A 4) :
    60480 ≤ Nat.card A := by
  rcases hm with hm | hm | hm
  · exact (sl_three_four_card hm).ge
  · obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    let := hF
    let := hfin
    rw [Nat.card_congr e.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hcard]
    norm_num
  · obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    let := hF
    let := hfin
    rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model,hcard]
    norm_num

private theorem local_eq_of_quotient_card_le
    {I J : Subgroup G} (hI : I ∈ Chapter1.L G T) (hJ : J ∈ Chapter1.L G T)
    (hIJ : I ≤ J)
    (hc : Nat.card (J ⧸ pCore 2 J) ≤ Nat.card (I ⧸ pCore 2 I)) : I = J := by
  let H := J ⊔ (T : Subgroup G)
  have hIH : I ≤ H := hIJ.trans le_sup_left
  let P := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hb : I.subgroupOf H ∈ Chapter1.L H (P : Subgroup H) :=
    (Chapter1.mem_LIn_iff_subgroupOf le_sup_right hIH).mp ⟨hIH,hI⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  let j := subgroupOfEquivOfLe (show J ≤ H from le_sup_left)
  let jq := QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
  let e : (J.subgroupOf H).map q ≃* (J ⧸ pCore 2 J) :=
    (cComponentTwoCoreQuotientEquiv hJ.1).symm.trans jq
  let b := subgroupOfEquivOfLe hIH
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  have hk : IsPGroup 2 (q.subgroupMap (I.subgroupOf H)).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let a := MonoidHom.quotientPCoreEquivOfSurjective (q.subgroupMap (I.subgroupOf H))
    (q.subgroupMap_surjective _) hk
  have hh : Nat.card ((J.subgroupOf H).map q) ≤ Nat.card ((I.subgroupOf H).map q) := by
    calc
      _ = Nat.card (J ⧸ pCore 2 J) := Nat.card_congr e.toEquiv
      _ ≤ Nat.card (I ⧸ pCore 2 I) := hc
      _ = Nat.card (((I.subgroupOf H).map q) ⧸ pCore 2 ((I.subgroupOf H).map q)) :=
        Nat.card_congr (bq.symm.trans a).toEquiv
      _ ≤ Nat.card ((I.subgroupOf H).map q) :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have he := Subgroup.eq_of_le_of_card_ge (map_mono (f := q) (comap_mono hIJ)) hh
  have hij := MovedMaximality.eq_of_twoCore_images_eq P hb.1 hJ.1 (comap_mono hIJ) he
  change I.subgroupOf H = J.subgroupOf H at hij
  simpa only [map_subgroupOf_eq_of_le hIH,map_subgroupOf_eq_of_le (show J ≤ H from le_sup_left)]
    using congrArg (map H.subtype) hij

/-- None of the three recognized third-vertex models can enlarge inside
one of those models, PSL₃(4), or ³D₄(4). The special-linear cover is handled by its actual
order; the other rows use the cubic rank and the original full Sylow. -/
theorem local_eq_of_triangle_models
    {I J : Subgroup G} (hI : I ∈ Chapter1.L G T) (hJ : J ∈ Chapter1.L G T)
    (hIJ : I ≤ J) (hr : 2 ≤ primeRank 3 I)
    (hmI : Source.IsSL (I ⧸ pCore 2 I) 3 4 ∨ Source.IsSp (I ⧸ pCore 2 I) 2 4 ∨
      ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4)
    (hmJ : Source.IsSL (J ⧸ pCore 2 J) 3 4 ∨
      ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 4 ∨
      Source.IsSp (J ⧸ pCore 2 J) 2 4 ∨ ClassificationModels.IsG2At (J ⧸ pCore 2 J) 4 ∨
      Triality.Standard.IsTrialityGroupAt 4 (J ⧸ pCore 2 J)) :
    I = J := by
  rcases hmJ with hs | hm
  · apply local_eq_of_quotient_card_le hI hJ hIJ
    rw [sl_three_four_card hs]
    exact triangle_card_lower hmI
  · exact local_eq_of_field_four_rank_two_overgroup hI hJ hIJ hr hm

/-- A normalized faithful local component of cubic rank two has a normalized
faithful maximal overcomponent with quasisimple two-core quotient. The
original global source exclusions and the literal chosen-module construction
survive this passage. This does not assert equality with the smaller group. -/
theorem exists_maximal_faithful_envelope
    {L₀ : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L₀)
    (hL : L ∈ Chapter1.L G T)
    (hf : L ∈ MainForward.faithfulLocalComponents T)
    (hn : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hr : 2 ≤ primeRank 3 L) :
    ∃ J : Subgroup G, L ≤ J ∧
      (T : Subgroup G) ≤ normalizer (J : Set G) ∧
      Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      ∃ W : Subgroup G, Nonempty (ChosenModule T J W) := by
  obtain ⟨J,hJ,hLJ⟩ := Chapter1.exists_mem_LStar_ge hL
  have hTJ := local_chain_normalizes hL hJ.1 hLJ hn
  have hfaith := faithful_local_overgroup T (h.simpleQTKE.evenCharacteristic T) hf hJ.1 hLJ
  let H := J ⊔ (T : Subgroup G)
  let R := H.pCoreIn 2
  let N := normalizer (R : Set G)
  have hHN : H ≤ N := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hH : IsSQTK KnownSimple.IsKnownSimple H := by
    have hh := (h.simpleQTKE.twoLocal_sqtk
      (show IsTwoLocal N from ⟨R,hJ.1.2.2,isPGroup_pCoreIn 2 H,rfl⟩)).subgroup
      (H.subgroupOf N)
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp hh
  have hrJ : 2 ≤ primeRank 3 J := hr.trans
    (_root_.primeRank_le_of_injective 3 (inclusion hLJ) (inclusion_injective hLJ))
  have hq := relative_quotient_quasisimple_of_three_rank hH ⟨le_sup_left,hJ.1.1⟩ hrJ
  have hsource : Hypothesis1223 KnownSimple.IsKnownSimple T J := {
    simpleQTKE := h.simpleQTKE
    maximal_faithful := ⟨hJ,hfaith.2⟩
    quasisimple := hq
    no_rankTwo := h.no_rankTwo
    no_M22 := h.no_M22
    no_M23 := h.no_M23
    no_J4 := h.no_J4 }
  exact ⟨J,hLJ,hTJ,hsource,hsource.toHypothesis1221.exists_chosen_of_normalizes hTJ⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
