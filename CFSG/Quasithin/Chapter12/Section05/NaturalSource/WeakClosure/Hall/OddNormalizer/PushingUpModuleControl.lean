module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpNormalizer
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Bounds
public import Theory.ElementaryAbelian.PrimeRankCard
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.RadicalInnerNormalizer
/-!
# The original exterior module in the enlarged pushing-up normalizer

Two distinct commuting copies of the exterior module would inject their
rank-twenty elementary direct product into the full component's central
quotient, the actual J₄ carrier of two-rank eleven. The central kernel is
removed using the fixed-free action of the original covering residual.
Thus the section-centralizer conjugate in the full source module equals
the original V. Reconstructing C.2.8 on a Sylow section centralizer proves
that every binary section-centralizing overgroup of the counterexample
core centralizes this same V, including the literal enlarged R₁.

Radical saturation also gives R = (R ∩ K) C_R(K), retaining the entire
covering center. Its nontrivial second factor is disjoint from V. Combined
with the checked commutator obstruction, the current chosen involution
has an R₁-commutator outside V. The remaining source step must identify
the component intersection modulo the covering center and choose an
involution fixed modulo V; neither follows from centralization alone.
The separate odd-local comparison on p.623 remains required.

Source: Aschbacher--Smith, 4.2.13, printed p.612. OddNormalizer applies
these results to the original exterior Hall counterexample.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 Chapter12.Section02
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

omit [Finite G] in
private theorem cover_fixed_eq_bot (s : SylowExteriorMarking D)
    {F : Subgroup G} (hcover : (L : Set G) = (F : Set G) * (L.pCoreIn 2 : Set G)) :
    V ⊓ centralizer (F : Set G) = ⊥ := by
  apply bot_unique
  intro v hv
  have hcore : L.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  apply s.marking.fixed_eq_bot ▸ (show v ∈ V ⊓ centralizer (L : Set G) from ?_)
  refine ⟨hv.1,?_⟩
  intro l hl
  obtain ⟨f,hf,q,hq,rfl⟩ := hcover ▸ hl
  exact (show Commute f v from hv.2 f hf).mul_left
    (show Commute q v from (hcore hq v hv.1).symm)

private def commutingProduct (K B C : Subgroup G) (hBK : B ≤ K) (hCK : C ≤ K)
    (hBC : B ≤ centralizer (C : Set G)) : B × C →* K where
  toFun x := ⟨x.1 * x.2,K.mul_mem (hBK x.1.property) (hCK x.2.property)⟩
  map_one' := Subtype.ext (one_mul _)
  map_mul' x y := by
    apply Subtype.ext
    change ((x.1 : G) * y.1) * ((x.2 : G) * y.2) =
      ((x.1 : G) * x.2) * ((y.1 : G) * y.2)
    rw [mul_assoc,←mul_assoc (y.1 : G),←hBC y.1.property x.2 x.2.property,
      mul_assoc,mul_assoc]

omit [Finite G] in
private theorem commutingProduct_quotient_injective
    (K F B C : Subgroup G) (hFK : F ≤ K) (hBK : B ≤ K) (hCK : C ≤ K)
    (hBC : B ≤ centralizer (C : Set G))
    (hFB : F ≤ normalizer (B : Set G)) (hFC : F ≤ normalizer (C : Set G))
    (hdis : B ⊓ C = ⊥) (hBfix : B ⊓ centralizer (F : Set G) = ⊥)
    (hCfix : C ⊓ centralizer (F : Set G) = ⊥) :
    Function.Injective ((QuotientGroup.mk' (center K)).comp
      (commutingProduct K B C hBK hCK hBC)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hz : commutingProduct K B C hBK hCK hBC x ∈ center K :=
    (QuotientGroup.eq_one_iff _).mp hx
  have hfix : ∀ f ∈ F, (MulAut.conj f) ((x.1 : G) * x.2) = (x.1 : G) * x.2 := by
    intro f hf
    exact mul_inv_eq_of_eq_mul (congrArg K.subtype (mem_center_iff.mp hz ⟨f,hFK hf⟩))
  have hbf : (x.1 : G) ∈ centralizer (F : Set G) := by
    intro f hf
    have he : (x.1 : G)⁻¹ * (MulAut.conj f) x.1 =
        (x.2 : G) * ((MulAut.conj f) x.2)⁻¹ := by
      have hh := hfix f hf
      rw [map_mul] at hh
      exact (eq_mul_inv_iff_mul_eq.mpr (by rw [mul_assoc,hh,inv_mul_cancel_left]))
    have hb : (x.1 : G)⁻¹ * (MulAut.conj f) x.1 ∈ B :=
      B.mul_mem (B.inv_mem x.1.property)
        ((mem_normalizer_iff.mp (hFB hf) _).mp x.1.property)
    have hc : (x.1 : G)⁻¹ * (MulAut.conj f) x.1 ∈ C := by
      rw [he]
      exact C.mul_mem x.2.property (C.inv_mem
        ((mem_normalizer_iff.mp (hFC hf) _).mp x.2.property))
    have hh : (x.1 : G)⁻¹ * (MulAut.conj f) x.1 = 1 := (show _ ∈ (⊥ : Subgroup G) from hdis ▸ ⟨hb,hc⟩)
    exact mul_inv_eq_iff_eq_mul.mp (inv_mul_eq_one.mp hh).symm
  have hb1 : (x.1 : G) = 1 := (show _ ∈ (⊥ : Subgroup G) from hBfix ▸ ⟨x.1.property,hbf⟩)
  have hcf : (x.2 : G) ∈ centralizer (F : Set G) := by
    intro f hf
    have hh := hfix f hf
    simpa only [hb1,one_mul] using (mul_inv_eq_iff_eq_mul.mp hh)
  have hc1 : (x.2 : G) = 1 := (show _ ∈ (⊥ : Subgroup G) from hCfix ▸ ⟨x.2.property,hcf⟩)
  exact Prod.ext (Subtype.ext hb1) (Subtype.ext hc1)

/-- Two commuting copies of the exterior module in the same full J₄ cover
must coincide. The proof uses the actual central quotient and two-rank bound. -/
theorem exterior_pushingUp_commuting_copy_eq
    (s : SylowExteriorMarking D) {F K U : Subgroup G}
    (hFK : F ≤ K) (hVK : V ≤ K) (hUK : U ≤ K)
    (hVF : V ≤ F) (hFL : F ≤ L)
    (hcover : (L : Set G) = (F : Set G) * (L.pCoreIn 2 : Set G))
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (hU : IsElementaryAbelian 2 U) (hcard : Nat.card U = Nat.card V)
    (hVU : V ≤ centralizer (U : Set G))
    (hFU : F ≤ normalizer (U : Set G))
    (hfix : U ⊓ centralizer (F : Set G) = ⊥) : U = V := by
  have hFV : F ≤ normalizer (V : Set G) := hFL.trans D.normalizes
  have hn : F ≤ normalizer (V ⊓ U : Set G) :=
    (le_inf hFV hFU).trans inf_normalizer_le_normalizer_inf
  rcases s.marking.cover_irreducible hVF hFL hcover.subset (V ⊓ U) inf_le_left hn with hd | he
  · let f := e.toMonoidHom.comp ((QuotientGroup.mk' (center K)).comp
      (commutingProduct K V U hVK hUK hVU))
    have hi : Function.Injective f := e.injective.comp
      (commutingProduct_quotient_injective K F V U hFK hVK hUK hVU hFV hFU
        hd (cover_fixed_eq_bot s hcover) hfix)
    have hr := (Theory.GroupTheory.primeRank_le_of_injective 2 f hi).trans Janko4.TwoRank.model_twoRank_le_eleven
    let := D.elementary
    let := hU
    have hVrank : primeRank 2 V = 10 := by
      have hh := IsElementaryAbelian.log_card_eq_primeRank (p := 2) V
      rw [s.marking.card_module] at hh
      exact hh.symm
    have hUrank : primeRank 2 U = 10 := by
      have hh := IsElementaryAbelian.log_card_eq_primeRank (p := 2) U
      rw [hcard,s.marking.card_module] at hh
      exact hh.symm
    rw [primeRank_prod_eq_add,hVrank,hUrank] at hr
    omega
  · exact (eq_of_le_of_card_ge (he.symm.le.trans inf_le_right) hcard.le).symm

omit [Finite G] in
private theorem fixed_cover (B F L Q : Subgroup G)
    (hfix : B ⊓ centralizer (L : Set G) = ⊥)
    (hQ : Q ≤ centralizer (B : Set G))
    (hcover : (L : Set G) = (F : Set G) * (Q : Set G)) :
    B ⊓ centralizer (F : Set G) = ⊥ := by
  apply bot_unique
  intro b hb
  apply hfix ▸ (show b ∈ B ⊓ centralizer (L : Set G) from ?_)
  refine ⟨hb.1,?_⟩
  intro l hl
  obtain ⟨f,hf,q,hq,rfl⟩ := hcover ▸ hl
  exact (show Commute f b from hb.2 f hf).mul_left
    (show Commute q b from (hQ hq b hb.1).symm)

omit [Finite G] in
/-- The fixed-free cover calculation survives the literal N(L) conjugator. -/
theorem exterior_pushingUp_conjugate_cover_fixed_eq_bot
    (s : SylowExteriorMarking D) {F : Subgroup G}
    (hcover : (L : Set G) = (F : Set G) * (L.pCoreIn 2 : Set G))
    (c : G) (hc : c ∈ normalizer (L : Set G)) :
    V.map (MulAut.conj c).toMonoidHom ⊓ centralizer (F : Set G) = ⊥ := by
  let a := MulAut.conj c
  have hLc : L.map a.toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp hc
  have hfix := congrArg (map a.toMonoidHom) s.marking.fixed_eq_bot
  rw [Subgroup.map_inf _ _ _ a.injective,map_centralizer_equiv,Subgroup.map_bot] at hfix
  change V.map a.toMonoidHom ⊓ centralizer (L.map a.toMonoidHom : Set G) = ⊥ at hfix
  rw [hLc] at hfix
  have hcore : L.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  have hc' := (map_mono (f := a.toMonoidHom) hcore).trans
    (map_centralizer_le_centralizer_image (V : Set G) a.toMonoidHom)
  rw [map_pCoreIn_of_injective 2 _ _ a.injective,hLc] at hc'
  exact fixed_cover _ F L (L.pCoreIn 2) hfix hc' hcover

/-- Every binary section-centralizing subgroup over the original counterexample
core centralizes the original exterior module, not merely a conjugate module. -/
theorem exterior_pushingUp_signalizer_centralizes
    (s : SylowExteriorMarking D) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A J H W P : Subgroup G} (hw : Witness L V A J H W)
    (hP : IsPGroup 2 P) (hPC : P ≤ sectionCentralizerIn s.marking.M L)
    (hRP : J.pCoreIn 2 ≤ P) : P ≤ centralizer (V : Set G) := by
  let M := normalizer (L : Set G)
  let C := sectionCentralizerIn M L
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hM := exterior_component_sylow_unique s h
  have hyp := source_hypothesis411 h.toHypothesis1221 hM
  have hm : coveringOvergroup M L (oddActorResidual L A) ∈ sigma M L := by
    refine ⟨sup_le (((oddActorResidual_le L A).trans inf_le_left).trans L.le_normalizer)
      inf_le_left,sup_le ?_ le_sup_right⟩
    intro l hl
    obtain ⟨j,hj,q,hq,rfl⟩ := hw.1.1.1.2.2.1 hl
    exact mul_mem (hw.1.1.1.1 hj)
      ((show C ≤ coveringOvergroup M L (oddActorResidual L A) from le_sup_right)
        (componentCore_le_sectionCentralizer L.le_normalizer hq))
  obtain ⟨S,hPS⟩ := (hP.comap_subtype : IsPGroup 2 (P.subgroupOf C)).exists_le_sylow
  let Q := (S : Subgroup C).map C.subtype
  have hPQ : P ≤ Q := fun p hp => ⟨⟨p,hPC hp⟩,hPS hp,rfl⟩
  have hRQ := hRP.trans hPQ
  let W₀ := Chapter4.Section02.Unitary.fullModule L Q
  have hc := Chapter4.Section02.Unitary.source_C28_of_muStar h.toHypothesis1221 D hM hm
    hw.1 hw.2.2.1 hw.2.2.2.1
    (fun he => hw.2.2.2.2.1.ne (inf_eq_left.mpr he)) S hRQ
  obtain ⟨c,hQc,hVW⟩ := Chapter4.Section02.Unitary.exists_fullModule_comparison
    h.toHypothesis1221 D hM S
  let U := V.map (MulAut.conj (c : G)).toMonoidHom
  obtain ⟨K,hK,hn,⟨e⟩,_,_⟩ := exterior_pushingUp_witness_janko s h hw
  let Kg := K.map H.subtype
  let eg := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let eq := (centerQuotientCongr eg).trans e
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK : F ≤ Kg := by
    have hh := map_mono (f := H.subtype) (hc.ordinary_component_contains_original K hK)
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  have hVF : V ≤ F := hw.2.2.2.2.2.2.2.2.2.2.1
  have hWH : W₀ ≤ H := hc.module_le_center_radical.trans
    ((map_subtype_le _).trans (hc.radical_le.trans hc.local_le))
  have hWK : W₀ ≤ Kg := by
    have hh := map_mono (f := H.subtype) ((hc.ordinary_module_placement K hK).1.trans inf_le_right)
    rwa [map_subgroupOf_eq_of_le hWH] at hh
  have hLc : L.map (MulAut.conj (c : G)).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp c.property.1
  have hLU : L ≤ normalizer (U : Set G) := by
    have hh := map_mono (f := (MulAut.conj (c : G)).toMonoidHom) D.normalizes
    rwa [hLc,map_equiv_normalizer_eq] at hh
  have hUC : U ≤ centralizer (J.pCoreIn 2 : Set G) := by
    intro u hu r hr
    obtain ⟨z,hz,rfl⟩ := hc.module_le_center_radical (hVW hu)
    exact congrArg (J.pCoreIn 2).subtype (mem_center_iff.mp hz ⟨r,hr⟩)
  have hUV : U = V := exterior_pushingUp_commuting_copy_eq s hFK (hVF.trans hFK)
    (hVW.trans hWK) hVF ((map_subtype_le _).trans inf_le_left)
    hw.2.2.2.2.2.2.2.1 eq
    (by let := D.elementary; exact IsElementaryAbelian.map _)
    (card_map_of_injective (MulAut.conj (c : G)).injective)
    (le_centralizer_iff.mp (hUC.trans (centralizer_le hw.2.2.2.2.2.1)))
    (((map_subtype_le _).trans inf_le_left).trans hLU)
    (exterior_pushingUp_conjugate_cover_fixed_eq_bot s hw.2.2.2.2.2.2.2.1 c c.property.1)
  have hWO := (Chapter4.Section02.Unitary.fullModule_data hyp.plus_perfect
    (Chapter4.Section02.Unitary.sectionSylow_normalized hyp.plus_le hyp.plus_normal hyp.plus_perfect S)).1
  apply le_centralizer_iff.mp
  intro v hv p hp
  have ho := Stellmacher.mem_omegaOneCenterAmbient_iff Q v |>.mp
    (hWO (hVW (hUV.ge hv)))
  exact ho.2.2 p (hPQ hp)

/-- Radical saturation splits the actual core over the full component,
retaining the covering center. The exterior module is disjoint from the
nontrivial component-centralizing factor. Identifying the first factor
with V times the covering center remains a separate assertion. -/
theorem exterior_pushingUp_radical_split
    (s : SylowExteriorMarking D) {A J H W : Subgroup G}
    (hw : Witness L V A J H W) (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let R := J.pCoreIn 2
    let Kg := K.map H.subtype
    let C := R ⊓ centralizer (Kg : Set G)
    R = (R ⊓ Kg) ⊔ C ∧ V ⊓ C = ⊥ ∧ C ≠ ⊥ := by
  let R := J.pCoreIn 2
  let Kg := K.map H.subtype
  have hc := hw.2.2.2.2.2.2.1
  let := hc.ordinary_component_normal K hK
  let := hK.2
  have hZ : IsPGroup 2 (center K) := by
    rw [IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hc.oddCore_eq_bot K)]
    exact pCore_isPGroup
  have hi : R.subgroupOf H ≤ K ⊔ centralizer (K : Set H) := by
    rw [←Janko4.perfect_cover_normalizer K e,normalizer_eq_top]
    exact le_top
  have hs := radical_eq_inf_sup_centralizer K (R.subgroupOf H) hc.isRadical hZ hi
  have hRH : R ≤ H := (pCoreIn_le 2 J).trans hw.2.2.2.1
  have hsG := congrArg (map H.subtype) hs
  rw [map_subgroupOf_eq_of_le hRH,Subgroup.map_sup,
    Subgroup.map_inf _ _ _ H.subtype_injective,
    Subgroup.map_inf _ _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le hRH,map_centralizer_subtype] at hsG
  have hsplit : R = (R ⊓ Kg) ⊔ (R ⊓ centralizer (Kg : Set G)) := by
    simpa only [←inf_assoc,inf_eq_left.mpr hRH] using hsG
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK : F ≤ Kg := by
    have hh := map_mono (f := H.subtype) (hc.ordinary_component_contains_original K hK)
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  have hdis : V ⊓ (R ⊓ centralizer (Kg : Set G)) = ⊥ := by
    apply bot_unique
    exact (inf_le_inf_left _ (inf_le_right.trans (centralizer_le hFK))).trans_eq
      (cover_fixed_eq_bot s hw.2.2.2.2.2.2.2.1)
  obtain ⟨r,_,hr,ho,hCr⟩ := residual_core_involution hw K hK
  refine ⟨hsplit,hdis,?_⟩
  intro he
  have hrC : r ∈ centralizer (Kg : Set G) := by
    intro k hk
    exact mem_centralizer_singleton_iff.mp (hCr (mem_sup_left hk))
  have hr1 : r = 1 := (show r ∈ (⊥ : Subgroup G) from he ▸ ⟨hr,hrC⟩)
  rw [hr1,orderOf_one] at ho
  omega

/-- The literal source normalizer now centralizes the original V. -/
@[expose] def ExteriorPushingUpControlledNormalizerData
    (T : Sylow 2 G) (L V J H H' : Subgroup G) (r : G) : Prop :=
  ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
      let P := (L ⊔ (((c : G) • T : Sylow 2 G) : Subgroup G)).pCoreIn 2
      let R := J.pCoreIn 2
      let R₁ := P ⊓ normalizer (R : Set G)
      let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      P = ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom ∧
      P = sectionCentralizerIn (((c : G) • T : Sylow 2 G) : Subgroup G) L ∧
      L ⊔ (((c : G) • T : Sylow 2 G) : Subgroup G) = L ⊔ P ∧
      R < P ∧ P ⊓ H' = R ∧ R < R₁ ∧ IsPGroup 2 R₁ ∧
      F ≤ normalizer (R₁ : Set G) ∧
      R₁ ⊓ centralizer ({r} : Set G) = R ∧
      V ≤ centralizer (R₁ : Set G) ∧
      ∃ q ∈ R₁, ⁅r,q⁆ ∉ V

/-- The original exterior branch with module centralization and full radical splitting. -/
@[expose] def ExteriorPushingUpModuleControlCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ s.marking.M.subgroupOf H ∧
    1024 ≤ Nat.card W ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    Nonempty ((F ⧸ pCore 2 F) ≃* Representation.SL5TenDimensional.Group) ∧
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ s.marking.M).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      V ≤ K.map H.subtype ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ (x : F) (k : K), ((k : H) : G) = (x : G) ∧ orderOf x = 3 ∧ orderOf k = 3 ∧
        16 ≤ Nat.card (V ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) ∧
        let R := solvableResidual (centralizer ({k} : Set K))
        (IsQuasisimple R ∧ Nonempty ((R ⧸ center R) ≃* Sporadic.Mathieu.M22) ∧
          IsComponent (centralizer ({(k : H)} : Set H))
            (R.map (K.subtype.elementCentralizerMap k)) ∧
          R.IsCComponent ∧ IsM22Cover (R ⧸ pCore 2 R) ∧
          (R.map (K.subtype.elementCentralizerMap k)).Normal ∧
          (⟨k,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({k} : Set K)) ∈ R ∧
          Nonempty ((R ⧸ solvableRadical R) ≃* Sporadic.Mathieu.M22) ∧
          ¬ R.map (H.subtype.comp (K.subtype.comp
            (centralizer ({k} : Set K)).subtype)) ≤ s.marking.M) ∧
        let I := F ⊔ J.pCoreIn 2
        I.pCoreIn 2 = J.pCoreIn 2 ∧ PushLE L J I ∧
          ∃ (r : G) (H' W' : Subgroup G),
            r ∈ H.pCoreIn 2 ∧ r ∈ J.pCoreIn 2 ∧ orderOf r = 2 ∧
            K.map H.subtype ⊔ J.pCoreIn 2 ≤ centralizer ({r} : Set G) ∧
            centralizer ({r} : Set G) ≤ H' ∧ Witness L V A I H' W' ∧
            IsComponentIn (K.map H.subtype) (centralizer ({r} : Set G)) ∧
            ((K.map H.subtype).subgroupOf (centralizer ({r} : Set G))).Normal ∧
            let Rg := R.map (H.subtype.comp (K.subtype.comp
              (centralizer ({k} : Set K)).subtype))
            let C := centralizer ({r} : Set G) ⊓ centralizer ({((k : H) : G)} : Set G)
            IsComponentIn Rg C ∧ (Rg.subgroupOf C).Normal ∧
            let X := centralizer ({((k : H) : G)} : Set G)
            IsComponentIn Rg X ∧ (Rg.subgroupOf X).Normal ∧
              ⁅zpowers r, X⁆ ≤ centralizer (Rg : Set G) ∧
              (∃ v ∈ V, v ∈ X ∧ v ∉ centralizer (Rg : Set G)) ∧
              (∀ Q : Subgroup G, IsPGroup 2 Q → V ≤ centralizer (Q : Set G) →
                F ≤ normalizer (Q : Set G) → (∀ q ∈ Q, ⁅r,q⁆ ∈ V) →
                Q ≤ centralizer ({r} : Set G)) ∧
              (J.pCoreIn 2 = (J.pCoreIn 2 ⊓ K.map H.subtype) ⊔
                (J.pCoreIn 2 ⊓ centralizer (K.map H.subtype : Set G))) ∧
              V ⊓ (J.pCoreIn 2 ⊓ centralizer (K.map H.subtype : Set G)) = ⊥ ∧
              J.pCoreIn 2 ⊓ centralizer (K.map H.subtype : Set G) ≠ ⊥ ∧
              ExteriorPushingUpControlledNormalizerData T L V J H H' r

/-- Centralize the original V with the literal R₁, retain the full radical
splitting, and isolate the remaining fixed-modulo-V involution obstruction. -/
theorem exterior_pushingUp_module_control_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A : Subgroup G} (hj : ExteriorPushingUpNormalizerCase s A) :
    ExteriorPushingUpModuleControlCase s A := by
  obtain ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,hres,hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hw',hKc,hKn,hRc,hRn,
    hRcX,hRnX,hcomm,hmoved,hvanish,c,hPc,hPsec,hgen,hlt,hPH,hlt₁,hR₁,hFN,hcent,q,hq,hqr⟩ := hj
  obtain ⟨hs,hd,hne⟩ := exterior_pushingUp_radical_split s hw K hK e
  refine ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,hres,hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hw',hKc,hKn,hRc,hRn,
    hRcX,hRnX,hcomm,hmoved,hvanish,hs,hd,hne,?_⟩
  let P := (L ⊔ (((c : G) • T : Sylow 2 G) : Subgroup G)).pCoreIn 2
  let R₁ := P ⊓ normalizer (J.pCoreIn 2 : Set G)
  have hPC : P ≤ sectionCentralizerIn s.marking.M L := by
    change (L ⊔ (((c : G) • T : Sylow 2 G) : Subgroup G)).pCoreIn 2 ≤ _
    rw [hPsec]
    intro p hp
    exact ⟨((le_sectionCentralizer_iff (sectionCentralizer L) L).mp le_rfl).1 hp.2,hp.2⟩
  have hPV : P ≤ centralizer (V : Set G) :=
    exterior_pushingUp_signalizer_centralizes s h hw' (isPGroup_pCoreIn 2 _)
      hPC (hcore.le.trans hlt.le)
  have hVR₁ : V ≤ centralizer (R₁ : Set G) :=
    le_centralizer_iff.mp (inf_le_left.trans hPV)
  have hnot : ¬ ∀ b ∈ R₁, ⁅r,b⁆ ∈ V := by
    intro hb
    have hh := hvanish R₁ hR₁ hVR₁ hFN hb hq
    exact hqr (mem_centralizer_singleton_iff.mp hh).symm
  push Not at hnot
  exact ⟨c,hPc,hPsec,hgen,hlt,hPH,hlt₁,hR₁,hFN,hcent,hVR₁,hnot⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
