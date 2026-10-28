module
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.ResidualCoreSelection
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpQuasisimple
public import Theory.GroupTheory.GeneralizedFitting.FullRankCentralProduct
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# The original exterior cubic in an involution centralizer

The residual-core replacement preserves source maximality and provides an
involution r in O₂(H), fixed by the full original covering component K.
Reconstructing C.2.8 on a maximal two-local over C_G(r) gives an ordinary
J₄ component there. Its cubic rank and central-product factorization force
it to equal the original K, retaining the entire cover. Thus K is an ordinary
normal component of C_G(r).

The already identified full residual at the original exterior cubic is
quasisimple. Its characteristicity in C_K(x), through the literal embedding,
now makes it a normal ordinary component of C_G(r) ∩ C_G(x). This supplies
the actual involution-centralizer input for I.3.2. Promotion to C_G(x), the
terminal commutator contradiction, and the separate p.623 odd-local comparison
remain required. The module of order at least 1024, PSL₅(2) section, original
cubic, sixteen fixed vectors and full Mathieu triple-cover quotient survive.

Source: Aschbacher--Smith 4.2.13, printed pp.611--612. OddNormalizer applies
this construction to the literal exterior Hall counterexample.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 Chapter12.Section02
open Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

private theorem normal_of_binaryFive_core_quotient
    {B : Subgroup G} (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hB : B.IsCComponent)
    (e : (B ⧸ pCore 2 B) ≃* Representation.SL5TenDimensional.Group) : B.Normal := by
  let Q := Representation.SL5TenDimensional.Group
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup Q := Representation.SL5TenDimensional.projectiveEquiv.isSimpleGroup
  let : Group.IsPerfect Q := Atlas.sl_perfect 5 (by decide)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.isSimpleGroup
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    rcases (inferInstance : (center (B ⧸ pCore 2 B)).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · let : Group.IsPerfect (B ⧸ pCore 2 B) :=
        Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
      exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht)).elim
  let : Group.IsPerfect (B ⧸ pCore 2 B) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsQuasisimple (B ⧸ pCore 2 B) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hr : 2 ≤ primeRank 3 (B ⧸ pCore 2 B) := by
    rw [primeRank_congr 3 (e.trans Representation.SL5TenDimensional.projectiveEquiv)]
    exact Theory.SpecificGroups.Classical.BinaryFiveRanks.projective_threeRank_ge_two
  exact hB.normal_of_coprime_core_center_primeRank (by decide : Odd 3)
    (by rw [hz]; simp) hr (hG.stronglyQuasithin 3 (by decide) (by decide))

/-- Every original exterior witness has an ordinary J₄ component, including
the witness reconstructed on the selected involution-centralizer overgroup. -/
theorem exterior_pushingUp_witness_janko (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W) :
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
      2 ≤ primeRank 3 K ∧ Nat.Coprime 3 (Nat.card (center K)) := by
  rcases hw with ⟨hJ,hpush,hH,hJH,hstrict,hVJ,hc,hcover,hN,hmove,hVF,⟨e,he⟩,hrest⟩
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let M := normalizer (L : Set G)
  have hw : Witness L V A J H W :=
    ⟨hJ,hpush,hH,hJH,hstrict,hVJ,hc,hcover,hN,hmove,hVF,⟨e,he⟩,hrest⟩
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  let := h.quasisimple
  let : IsQuasisimple (F ⧸ pCore 2 F) := IsQuasisimple.of_mulEquiv e.symm
  have hf : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H := by
    intro hf
    have hm : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) M :=
      exterior_component_sylow_unique s h
    have hd := reciprocal_setup hH hm.1 (h.simpleQTKE.twoLocal_sqtk hm.1.1)
      (fun he => hstrict.ne (by rw [he,inf_idem])) hf
    obtain ⟨hF,hnorm,hi⟩ := index_two_of_fitting_contained hc hN hstrict hd.1 hf
    let eq := subgroupOfEquivOfLe hFH
    let q := (QuotientGroup.congr _ _ eq (pCore_map_iso 2 eq)).trans
      (e.trans s.marking.quotientEquiv)
    let : (F.subgroupOf H).Normal := normal_of_binaryFive_core_quotient hc.sqtk hF q
    rw [normalizer_eq_top] at hnorm
    rw [←hnorm,index_top] at hi
    norm_num at hi
  have hf' : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (H ⊓ M).subgroupOf H :=
    fun hh => hf (hh.trans (comap_mono inf_le_right))
  obtain ⟨K,hK,hq,hout,hFK,hcases⟩ := hc.ordinary_or_constrained_escape hf'
  have hnF : H ⊓ M ≤ normalizer (F : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hN
  have hoK : IsComponent H K := hcases.resolve_right
    (exterior_no_constrained_pushingUp hc hnF (e.trans s.marking.quotientEquiv) K hK hq hout)
  have hFK' := hc.ordinary_component_contains_original K hoK
  have hFKg : F ≤ K.map H.subtype := by
    have hh := map_mono (f := H.subtype) hFK'
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  let : Group.IsPerfect F := Group.IsPerfect.map _
  let j : F →* K := (inclusion hFH).codRestrict K (fun f => hFK' f.property)
  have hj : Function.Injective j := fun a b he =>
    (inclusion_injective hFH) (congrArg K.subtype he)
  have hrF : 2 ≤ primeRank 3 F := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 F) pCore_isPGroup,
      primeRank_equiv 3 ((e.trans s.marking.quotientEquiv).trans
        Representation.SL5TenDimensional.projectiveEquiv)]
    exact Theory.SpecificGroups.Classical.BinaryFiveRanks.projective_threeRank_ge_two
  let := hoK.2
  have hz : IsPGroup 2 (center K) := by
    rw [IsQuasisimple.center_eq_pCore (hoK.1.pPrimeCore_eq_bot hc.oddCore_eq_bot K)]
    exact pCore_isPGroup
  obtain ⟨n,hn⟩ := hz.exists_card_eq
  exact ⟨K,hoK,hc.ordinary_component_normal K hoK,
    exterior_pushingUp_ordinary_janko s hw K hoK,
    hrF.trans (Theory.GroupTheory.primeRank_le_of_injective 3 j hj),
    by rw [hn]; exact (by decide : Nat.Coprime 3 2).pow_right n⟩

/-- The original J₄ cover remains a normal ordinary component in any
outside overgroup carrying a reselected exterior witness and containing it. -/
theorem exterior_pushingUp_component_in_reselected_overgroup
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A H I H' W' : Subgroup G}
    (hw' : Witness L V A I H' W')
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (hKH' : K.map H.subtype ≤ H') :
    IsComponent H' ((K.map H.subtype).subgroupOf H') ∧
      ((K.map H.subtype).subgroupOf H').Normal := by
  obtain ⟨N,hN,hn,⟨en⟩,hr,hz⟩ := exterior_pushingUp_witness_janko s h hw'
  let B := (K.map H.subtype).subgroupOf H'
  let eb : K ≃* B := (K.equivMapOfInjective H.subtype H.subtype_injective).trans
    (subgroupOfEquivOfLe hKH').symm
  let := hK.2
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eb
  let := hN.2
  let := hn
  have hp : N ⊔ centralizer (N : Set H') = ⊤ := by
    rw [←Janko4.perfect_cover_normalizer N en,normalizer_eq_top]
  let eqb : (B ⧸ center B) ≃* Janko4.Model := (centerQuotientCongr eb).symm.trans e
  have heq : B = N := quasisimple_eq_of_full_rank_central_product (p := 3) B N hp hz hr
    (hw'.2.2.2.2.2.2.1.sqtk.stronglyQuasithin 3 (by decide) (by decide))
    (by rw [Nat.card_congr eqb.toEquiv,Janko4.Cardinality.model_card]; decide)
    (by rw [Nat.card_congr eqb.toEquiv,Nat.card_congr en.toEquiv])
  change IsComponent H' B ∧ B.Normal
  rw [heq]
  exact ⟨hN,hn⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 Chapter12.Section02
open Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Construct the source involution and promote the original full cover to
its full ambient centralizer, using the reselected C.2.8 witness. -/
theorem exterior_pushingUp_selected_involution
    (s : SylowExteriorMarking D) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (hout : ¬ K ≤ (H ⊓ s.marking.M).subgroupOf H) :
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let I := F ⊔ J.pCoreIn 2
    I.pCoreIn 2 = J.pCoreIn 2 ∧ PushLE L J I ∧
      ∃ (r : G) (H' W' : Subgroup G),
        r ∈ H.pCoreIn 2 ∧ r ∈ J.pCoreIn 2 ∧ orderOf r = 2 ∧
        K.map H.subtype ⊔ J.pCoreIn 2 ≤ centralizer ({r} : Set G) ∧
        centralizer ({r} : Set G) ≤ H' ∧ Witness L V A I H' W' ∧
        IsComponentIn (K.map H.subtype) (centralizer ({r} : Set G)) ∧
        ((K.map H.subtype).subgroupOf (centralizer ({r} : Set G))).Normal := by
  have hc := hw.2.2.2.2.2.2.1
  obtain ⟨hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hKH',hw'⟩ :=
    selected_involution_witness h.toHypothesis1221 D
      (exterior_component_sylow_unique s h) hw K hK
      (hc.ordinary_component_contains_original K hK) hout
  obtain ⟨hK',hn⟩ := exterior_pushingUp_component_in_reselected_overgroup s h hw' K hK e hKH'
  have hKC : K.map H.subtype ≤ centralizer ({r} : Set G) := le_sup_left.trans hCr
  have hnorm : H' ≤ normalizer (K.map H.subtype : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH').mp hn
  exact ⟨hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hw',
    (show IsComponentIn (K.map H.subtype) H' from ⟨hKH',hK'⟩).restrict hKC hCH',
    normal_subgroupOf_of_le_normalizer (hCH'.trans hnorm)⟩

omit [Finite G] in
private theorem residual_image_normal
    {E : Type*} [Group E] [Finite E]
    (f : E →* G) (hf : Function.Injective f) (x : E) (C : Subgroup G)
    (hCN : C ≤ normalizer (f.range : Set G))
    (hCx : C ≤ centralizer ({f x} : Set G)) :
    C ≤ normalizer (((solvableResidual (centralizer ({x} : Set E))).map
      (f.comp (centralizer ({x} : Set E)).subtype)) : Set G) := by
  let B := centralizer ({x} : Set E)
  let X := f.range ⊓ centralizer ({f x} : Set G)
  have hX : B.map f = X := by
    ext y
    constructor
    · rintro ⟨b,hb,rfl⟩
      refine ⟨⟨b,rfl⟩,mem_centralizer_singleton_iff.mpr ?_⟩
      simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hb)
    · rintro ⟨⟨b,rfl⟩,hb⟩
      refine ⟨b,mem_centralizer_singleton_iff.mpr (hf ?_),rfl⟩
      simpa only [map_mul] using mem_centralizer_singleton_iff.mp hb
  let e : B ≃* X := (B.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hX)
  have hR : (solvableResidual B).map (f.comp B.subtype) =
      (solvableResidual X).map X.subtype := by
    rw [←map_solvableResidual_eq e.toMonoidHom e.surjective,map_map]
    rfl
  rw [hR]
  apply le_trans _ (normalizer_le_normalizer_characteristic_image X (solvableResidual X))
  exact (le_inf hCN (hCx.trans (centralizer ({f x} : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

/-- At the unchanged exterior cubic, the full residual is now an ordinary
normal component of C_G(r) ∩ C_G(x), the precise input to source I.3.2. -/
theorem exterior_pushingUp_cubic_residual_in_involution_centralizer
    (s : SylowExteriorMarking D) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K) (hn : K.Normal)
    (e : (K ⧸ center K) ≃* Janko4.Model) (k : K) (hk : orderOf k = 3)
    (r : G) (hKC : K.map H.subtype ≤ centralizer ({r} : Set G))
    (hKN : ((K.map H.subtype).subgroupOf (centralizer ({r} : Set G))).Normal) :
    let R := (solvableResidual (centralizer ({k} : Set K))).map
      (H.subtype.comp (K.subtype.comp (centralizer ({k} : Set K)).subtype))
    let C := centralizer ({r} : Set G) ⊓ centralizer ({((k : H) : G)} : Set G)
    IsComponentIn R C ∧ (R.subgroupOf C).Normal := by
  let f := H.subtype.comp K.subtype
  have hf : Function.Injective f := H.subtype_injective.comp K.subtype_injective
  let Q := solvableResidual (centralizer ({k} : Set K))
  let R := Q.map (f.comp (centralizer ({k} : Set K)).subtype)
  let C := centralizer ({r} : Set G) ⊓ centralizer ({((k : H) : G)} : Set G)
  have hrange : f.range = K.map H.subtype := by
    rw [MonoidHom.range_comp,range_subtype]
  have hCN : C ≤ normalizer (f.range : Set G) := by
    rw [hrange]
    exact inf_le_left.trans ((normal_subgroupOf_iff_le_normalizer hKC).mp hKN)
  have hRN := residual_image_normal f hf k C hCN inf_le_right
  have hRC : R ≤ C := by
    rintro z ⟨q,hq,rfl⟩
    refine ⟨hKC (mem_map_of_mem H.subtype q.val.property),mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg f (mem_centralizer_singleton_iff.mp q.property)
  let hnormal : (R.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer hRN
  let := exterior_pushingUp_cubic_residual_quasisimple s h hw K hK hn e k hk
  let eq : Q ≃* R.subgroupOf C :=
    (Q.equivMapOfInjective (f.comp (centralizer ({k} : Set K)).subtype)
      (hf.comp (centralizer ({k} : Set K)).subtype_injective)).trans
        (subgroupOfEquivOfLe hRC).symm
  exact ⟨⟨hRC,hnormal.isSubnormal,IsQuasisimple.of_mulEquiv eq⟩,hnormal⟩
end CFSG.Quasithin.Chapter12.Section05.NaturalSource

namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 Chapter12.Section02
open Chapter4.Section02.RankOneReciprocalEscape Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The original full cubic residual, with the constructed involution and
its precise ordinary-component placement in the simultaneous centralizer. -/
@[expose] def ExteriorPushingUpInvolutionResidualCase (s : SylowExteriorMarking D)
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
            IsComponentIn Rg C ∧ (Rg.subgroupOf C).Normal

/-- Preserve the original exterior cubic and its full residual through the
involution-centralizer selection and ordinary-component promotion. -/
theorem exterior_pushingUp_involution_residual_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A : Subgroup G} (hj : ExteriorPushingUpOrdinaryResidualCase s A) :
    ExteriorPushingUpInvolutionResidualCase s A := by
  obtain ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,hres⟩ := hj
  obtain ⟨hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hw',hKc,hKn⟩ :=
    exterior_pushingUp_selected_involution s h hw K hK e hout
  exact ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,hres,hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hw',hKc,hKn,
    exterior_pushingUp_cubic_residual_in_involution_centralizer s h hw K hK hn e k hk r hKc.1 hKn⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
