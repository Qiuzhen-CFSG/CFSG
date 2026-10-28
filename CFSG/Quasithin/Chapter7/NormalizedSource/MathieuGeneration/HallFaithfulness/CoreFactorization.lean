module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicTrivialDisplacement
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.ResidualCoreSelection
public import Theory.Mathieu.InnerCoreJoin
public import Theory.GroupTheory.RadicalInnerNormalizer
public import Theory.GroupTheory.NormalClosureCentralizerCore

/-!
# Core factors and involution reselection in the Mathieu pushing-up branch

For the M₂₃ and M₂₄ central quotients the literal local join is L O₂(LT).
The multiplier and automorphism calculations prove this factorization on
the original quotient; the M₁₂ and M₂₂ rows remain explicit alternatives.
Consequently each containing section Sylow strictly enlarges O₂(J) in the
inner rows.

Radical saturation factors R = O₂(J) into R intersect K and C_R(K), where
K is the full original J₄ covering component. The factors commute, and
their overlap is exactly the embedded Z(K). The original chosen module
lies in the first factor and has trivial intersection with the second.
No equality R intersect K = V or triviality of the covering kernel is used.

Every involution centralizing R and the full K has centralizer R in any
containing section Sylow. To prove this, replace J by its intersection
residual joined with R, rebuild the genuine source witness over the
involution centralizer, and apply the already proved Sylow intersection.
Thus the cubic vanishing argument applies to any such involution in R,
without restricting the eventual choice to O₂(H).

The literal Hall consumer retains every earlier witness and constructs
these additional conclusions. The component-factor identification, an
involution giving the full displacement domain, and the separate M₂₄
fixed-line and odd-actor comparisons remain to be established.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612; 4.4.14, pp.624--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The M23 and M24 rows give the source factorization with the literal local core. -/
theorem sourceOrbit_mathieu_inner_localJoin
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M23) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M24)) :
    L ⊔ (T : Subgroup G) = L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let := h.quasisimple
  apply Sporadic.Mathieu.m23_or_m24_core_join L (T : Subgroup G)
    D.sylow_normalizes_component T.isPGroup'
  exact hm.imp (fun e => ⟨(D.orbitCentralQuotientEquiv h).trans e.some⟩)
    (fun e => ⟨(D.orbitCentralQuotientEquiv h).trans e.some⟩)

/-- Failure of the local factorization retains only the actual M12 and M22 central quotients. -/
theorem sourceOrbit_mathieu_localJoin_alternatives
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm : HasMathieuCentralQuotient D.orbitComponent) :
    Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22) ∨
      L ⊔ (T : Subgroup G) = L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  rcases hm with h12 | h22 | h23 | h24
  · exact .inl h12
  · exact .inr (.inl h22)
  · exact .inr (.inr (D.sourceOrbit_mathieu_inner_localJoin h (.inl h23)))
  · exact .inr (.inr (D.sourceOrbit_mathieu_inner_localJoin h (.inr h24)))

/-- The literal section Sylows strictly enlarge the original core in the inner Mathieu rows. -/
theorem sourceOrbit_pushingUp_core_lt_of_inner_mathieu
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M23) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M24))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
    (hRP : J.pCoreIn 2 ≤ (P : Subgroup _).map
      (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) :
    J.pCoreIn 2 < (P : Subgroup _).map
      (sectionCentralizerIn (normalizer (L : Set G)) L).subtype := by
  apply D.sourceOrbit_pushingUp_core_lt_of_localJoin h hw _ P hRP
  exact (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right).trans_eq
    (D.sourceOrbit_mathieu_inner_localJoin h hm)

/-- Radical saturation factors the actual source core inside the full J4 cover.
The central overlap is retained explicitly. -/
theorem sourceOrbit_pushingUp_core_central_product
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let R := J.pCoreIn 2
    let Kg := K.map H.subtype
    R = (R ⊓ Kg) ⊔ (R ⊓ centralizer (Kg : Set G)) ∧
      ⁅R ⊓ Kg,R ⊓ centralizer (Kg : Set G)⁆ = ⊥ ∧
      (R ⊓ Kg) ⊓ (R ⊓ centralizer (Kg : Set G)) =
        (center K).map (H.subtype.comp K.subtype) := by
  let hc := hw.2.2.2.2.2.2.1
  let R := J.pCoreIn 2
  let Kg := K.map H.subtype
  have hRH : R ≤ H := (pCoreIn_le 2 J).trans hw.2.2.2.1
  let := hc.ordinary_component_normal K hK
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hc.oddCore_eq_bot K)
  have hi : R.subgroupOf H ≤ K ⊔ centralizer (K : Set H) := by
    rw [←Janko4.perfect_cover_normalizer K e,normalizer_eq_top]
    exact le_top
  have hs := radical_eq_inf_sup_centralizer K (R.subgroupOf H) hc.isRadical
    (hz.symm ▸ pCore_isPGroup) hi
  have hm := congrArg (map H.subtype) hs
  rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ H.subtype_injective,Subgroup.map_inf _ _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le hRH,map_centralizer_subtype] at hm
  have hRC : R ⊓ (H ⊓ centralizer (Kg : Set G)) = R ⊓ centralizer (Kg : Set G) := by
    rw [←inf_assoc,inf_eq_left.mpr hRH]
  rw [hRC] at hm
  have hZH : (center K).map K.subtype ≤ pCore 2 H := by
    apply le_sSup
    refine ⟨?_,(hz.symm ▸ pCore_isPGroup).map K.subtype⟩
    apply normalizer_eq_top_iff.mp
    apply top_unique
    simpa only [normalizer_eq_top] using
      normalizer_le_normalizer_characteristic_image K (center K)
  have hZR : (center K).map (H.subtype.comp K.subtype) ≤ R := by
    rw [←map_map]
    exact (map_mono hZH).trans hc.ambient_core_le_radical
  refine ⟨hm,?_,?_⟩
  · apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (le_centralizer_iff.mp (show R ⊓ centralizer (Kg : Set G) ≤
      centralizer (Kg : Set G) from inf_le_right)).trans' inf_le_right
  · rw [←inf_eq_right.mpr hZR]
    ext z
    constructor
    · rintro ⟨⟨hzR,k,hk,rfl⟩,hzR',hcK⟩
      refine ⟨hzR,⟨k,hk⟩,mem_center_iff.mpr ?_,rfl⟩
      intro y
      apply Subtype.ext
      apply Subtype.ext
      exact hcK ((y : H) : G) (mem_map_of_mem H.subtype y.property)
    · rintro ⟨hzR,k,hk,rfl⟩
      refine ⟨⟨hzR,mem_map_of_mem H.subtype k.property⟩,hzR,?_⟩
      rintro y ⟨y,hy,rfl⟩
      exact congrArg (fun k : K => ((k : H) : G)) (mem_center_iff.mp hk ⟨y,hy⟩)

include D in
/-- The actual chosen module has trivial intersection with the central factor.
The rest of the component intersection is not identified with V here. -/
theorem sourceOrbit_pushingUp_module_disjoint_central_factor
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K) :
    V ≤ J.pCoreIn 2 ⊓ K.map H.subtype ∧
      V ⊓ (J.pCoreIn 2 ⊓ centralizer (K.map H.subtype : Set G)) = ⊥ := by
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK : F ≤ K.map H.subtype := by
    have hh := map_mono (f := H.subtype)
      (hw.2.2.2.2.2.2.1.ordinary_component_contains_original K hK)
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  have hVF : V ≤ F := hw.2.2.2.2.2.2.2.2.2.2.1
  have hcore : L.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  refine ⟨le_inf hw.2.2.2.2.2.1 (hVF.trans hFK),bot_unique ?_⟩
  intro v hv
  apply hfix.le
  refine ⟨hv.1,?_⟩
  intro l hl
  obtain ⟨f,hf,q,hq,rfl⟩ := hw.2.2.2.2.2.2.2.1 ▸ (show l ∈ (L : Set G) from hl)
  calc
    (f*q)*v = f*(q*v) := mul_assoc _ _ _
    _ = f*(v*q) := congrArg (f * ·) ((hcore hq) v hv.1).symm
    _ = v*(f*q) := by rw [←mul_assoc,hv.2.2 f (hFK hf),mul_assoc]

include D in
/-- Every core-central involution fixing the full covering component has the
same original kernel in every containing section Sylow. Membership in O2(H)
is not required: the genuine outside witness is rebuilt over its centralizer. -/
theorem sourceOrbit_pushingUp_core_involution_kernel
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (r : G) (hr : orderOf r = 2)
    (hKr : K.map H.subtype ≤ centralizer ({r} : Set G))
    (hRr : J.pCoreIn 2 ≤ centralizer ({r} : Set G))
    (P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
    (hRP : J.pCoreIn 2 ≤ (P : Subgroup _).map
      (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) :
    (P : Subgroup _).map (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ⊓
      centralizer ({r} : Set G) = J.pCoreIn 2 := by
  have hM := h.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hjoin : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let I := F ⊔ J.pCoreIn 2
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK : F ≤ K.map H.subtype := by
    have hh := map_mono (f := H.subtype)
      (hw.2.2.2.2.2.2.1.ordinary_component_contains_original K hK)
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  obtain ⟨hcore,hpush,_,hI⟩ := residual_core_selection h D hjoin hw
  have hlocal : IsTwoLocal (centralizer ({r} : Set G)) := by
    refine ⟨zpowers r,?_,?_,(normalizer_zpowers_eq_centralizer_of_order_two r hr).symm⟩
    · intro hb
      have he := mem_zpowers r
      rw [hb,mem_bot] at he
      rw [he,orderOf_one] at hr
      omega
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hr,pow_one])
  obtain ⟨H',hH',hCH'⟩ :=
    exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot (centralizer ({r} : Set G)) (by
      intro hb
      exact (Chapter1.mem_H_of_isTwoLocal hlocal)
        (by simp only [pCoreIn,hb,Subgroup.map_bot]))
  have hIH' : I ≤ H' := (sup_le (hFK.trans hKr) hRr).trans hCH'
  have hout' : ¬ H' ≤ normalizer (L : Set G) := by
    intro hh
    apply hout
    intro k hk
    exact ⟨k.property,hh (hCH' (hKr (mem_map_of_mem H.subtype hk)))⟩
  obtain ⟨W',hw'⟩ := witness_on_selected_overgroup h D hjoin hw hpush hI hH' hIH' hout'
  have he := D.sourceOrbit_pushingUp_sectionSylow_centralizer h hw' r
    (hcore.le.trans hRr) hCH' P (hcore.le.trans hRP)
  exact he.trans hcore

/-- Vanishing holds for every admissible involution in the original core,
on its precisely defined displacement domain. This allows source reselection
outside O2(H), retaining the original cubic resolution and full J4 cover. -/
theorem sourceOrbit_pushingUp_core_involution_displacement
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit) (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (x : K) (hx : orderOf x = 3) (r₀ : G)
    (hfull : CubicPumpupFullResolution H K x r₀)
    (r : G) (hrR : r ∈ J.pCoreIn 2) (hr : orderOf r = 2)
    (hKr : K.map H.subtype ≤ centralizer ({r} : Set G))
    (hRr : J.pCoreIn 2 ≤ centralizer ({r} : Set G))
    (P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
    (hRP : J.pCoreIn 2 ≤ (P : Subgroup _).map
      (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) :
    let Pg := (P : Subgroup _).map (sectionCentralizerIn (normalizer (L : Set G)) L).subtype
    Pg ⊓ centralizer ({r} : Set G) = J.pCoreIn 2 ∧
      pushingDisplacementDomain Pg (J.pCoreIn 2) V r ≤ J.pCoreIn 2 ∧
      ⁅zpowers r,pushingDisplacementDomain Pg (J.pCoreIn 2) V r⁆ = ⊥ := by
  let := hw.2.2.2.2.2.2.1.ordinary_component_normal K hK
  have hFK := hw.2.2.2.2.2.2.1.ordinary_component_contains_original K hK
  have hc := D.sourceOrbit_pushingUp_core_involution_kernel h hw K hK hout r hr hKr hRr P hRP
  have hfull' := cubic_full_resolution_reselect H K x r₀ r hfull hKr
  have hQ := D.sourceOrbit_pushingUp_displacement_le_core h hV hm hfix hw K hFK e
    r hrR hKr x hx hfull' P hRP hc
  refine ⟨hc,hQ,?_⟩
  rw [commutator_comm,commutator_eq_bot_iff_le_centralizer,zpowers_eq_closure,centralizer_closure]
  exact hQ.trans hRr

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Sporadic.Mathieu Janko4.InvolutionCentralizers
/-- The full original configuration with the radical central product and its covering overlap. -/
@[expose] def MathieuPushingUpFactoredCase {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ((T : Subgroup G) ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
      ∀ P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L),
        J.pCoreIn 2 ≤ (P : Subgroup _).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype →
        J.pCoreIn 2 < (P : Subgroup _).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      (let R := J.pCoreIn 2
       let Kg := K.map H.subtype
       R = (R ⊓ Kg) ⊔ (R ⊓ centralizer (Kg : Set G)) ∧
         ⁅R ⊓ Kg,R ⊓ centralizer (Kg : Set G)⁆ = ⊥ ∧
         (R ⊓ Kg) ⊓ (R ⊓ centralizer (Kg : Set G)) =
           (center K).map (H.subtype.comp K.subtype) ∧
         V ≤ R ⊓ Kg ∧ V ⊓ (R ⊓ centralizer (Kg : Set G)) = ⊥) ∧
      (∀ s : G, s ∈ J.pCoreIn 2 → orderOf s = 2 →
        K.map H.subtype ≤ centralizer ({s} : Set G) →
        J.pCoreIn 2 ≤ centralizer ({s} : Set G) →
        ∀ P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L),
          let Pg := (P : Subgroup _).map (sectionCentralizerIn (normalizer (L : Set G)) L).subtype
          J.pCoreIn 2 ≤ Pg → Pg ⊓ centralizer ({s} : Set G) = J.pCoreIn 2 ∧
            pushingDisplacementDomain Pg (J.pCoreIn 2) V s ≤ J.pCoreIn 2 ∧
            ⁅zpowers s,pushingDisplacementDomain Pg (J.pCoreIn 2) V s⁆ = ⊥) ∧
      ∃ (r : H.pCoreIn 2) (H₁ : Subgroup G), orderOf r = 2 ∧
        centralizer ({(r : G)} : Set G) ≤ H₁ ∧
        IsComponentIn (K.map H.subtype) H₁ ∧
        ((K.map H.subtype).subgroupOf H₁).Normal ∧
        IsComponentIn (K.map H.subtype) (centralizer ({(r : G)} : Set G)) ∧
      ∃ e : (K ⧸ center K) ≃* Janko4.Model,
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
        let R := First.centralizer.comap q
        ∃ x : R, orderOf x = 3 ∧ orderOf (q (x : K)) = 3 ∧
          (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : Subgroup.centralizer ({x} : Set R)) ∈
            solvableResidual (Subgroup.centralizer ({x} : Set R)) ∧
          solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)) =
            (solvableResidual (Subgroup.centralizer ({x} : Set R))).map
              (R.subtype.elementCentralizerMap x) ∧
          IsQuasisimple (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ∧
          Nonempty (((solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ⧸
            center (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)))) ≃* M22) ∧
          (∃ g : K, ((g * (x : K) * g⁻¹ : K) : H) ∈ F.subgroupOf H ∧
            let y := g * (x : K) * g⁻¹
            IsQuasisimple (solvableResidual (centralizer ({y} : Set K))) ∧
              Nonempty ((solvableResidual (centralizer ({y} : Set K)) ⧸
                center (solvableResidual (centralizer ({y} : Set K)))) ≃* M22) ∧
              CubicAmbientData H K y ∧
              (let C := centralizer ({((y : H) : G)} : Set G) ⊓ centralizer ({(r : G)} : Set G)
               IsComponentIn (cubicResidualImage H K y) C ∧
                 ((cubicResidualImage H K y).subgroupOf C).Normal) ∧
              CubicPumpupData H K y (r : G) ∧
              CubicPumpupQuotientAction H K y (r : G) ∧
              CubicPumpupFullResolution H K y (r : G) ∧
              CubicTrivialDisplacementConclusion T L V J H K y (r : G) ∧
              ∀ Q : Subgroup (centralizer ({y} : Set K)), Q.IsCComponent →
                Q = solvableResidual (centralizer ({y} : Set K))) ∧
          ∀ Q : Subgroup (Subgroup.centralizer ({(x : K)} : Set K)), Q.IsCComponent →
            Q = solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))


end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- Factor the literal original core while preserving every cubic and displacement witness. -/
theorem pushingUp_core_factorization
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit) (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    {A : Subgroup G} (hc : MathieuPushingUpTrivialDisplacementCase T L V A) :
    MathieuPushingUpFactoredCase T L V A := by
  obtain ⟨J,H,W,hw,hstrict,hesc,K,hK,hn,hout,hFK,hWK,hprod,r,H₁,hr,hCH,hrel,hn₁,hKr,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hs,hp,hact,hfull,hdisp,huy⟩,hux⟩ := hc
  have hf := sourceOrbit_pushingUp_core_central_product hw K hK e
  have hv := D.sourceOrbit_pushingUp_module_disjoint_central_factor hfix hw K hK
  have hy : orderOf (g * (x : K) * g⁻¹) = 3 :=
    ((MulAut.conj g).orderOf_eq (x : K)).trans ((orderOf_coe x).trans hx)
  have hcontrol := D.sourceOrbit_pushingUp_core_involution_displacement h hV hm hfix hw
    K hK hout e (g * (x : K) * g⁻¹) hy (r : G) hfull
  exact ⟨J,H,W,hw,hstrict,hesc,K,hK,hn,hout,hFK,hWK,hprod,
    ⟨hf.1,hf.2.1,hf.2.2,hv.1,hv.2⟩,hcontrol,
    r,H₁,hr,hCH,hrel,hn₁,hKr,e,x,hx,hqx,hmem,he,hquasi,heq,
    ⟨g,hg,hqy,hey,hdata,hs,hp,hact,hfull,hdisp,huy⟩,hux⟩

/-- In the inner Mathieu rows, the original selected displacement domain is
proper in the full relative normalizer, with strict core growth proved. -/
theorem pushingUp_inner_mathieu_domain_proper
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M23) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M24))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    {K : Subgroup H} {x : K} {r : G}
    (hd : CubicTrivialDisplacementConclusion T L V J H K x r) :
    ∃ P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L),
      let Pg := (P : Subgroup _).map (sectionCentralizerIn (normalizer (L : Set G)) L).subtype
      J.pCoreIn 2 < Pg ∧ Pg ⊓ centralizer ({r} : Set G) = J.pCoreIn 2 ∧
        pushingDisplacementDomain Pg (J.pCoreIn 2) V r < Pg ⊓ normalizer (J.pCoreIn 2 : Set G) := by
  obtain ⟨P,hRP,hcent,hrest⟩ := hd.1
  have hg := D.sourceOrbit_mathieu_inner_localJoin h hm
  have hj : (T : Subgroup G) ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right).trans_eq hg
  have hq := hd.2.2 P hRP hcent
  refine ⟨P,D.sourceOrbit_pushingUp_core_lt_of_localJoin h hw hj P hRP,hcent,?_⟩
  exact lt_of_le_of_ne ((commutatorPreimage_le _ _ _).trans inf_le_left) (hq.2.2 hj)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal Hall consumer constructs the radical factors with their exact central overlap.
It retains the small Mathieu rows when the local-join factorization is not yet known. -/
theorem sourceOrbit_mathieu_hall_factored_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22) ∨
      L ⊔ (T : Subgroup G) = L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (MathieuPushingUpFactoredCase T L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_trivial_displacement_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine ⟨D.sourceOrbit_mathieu_localJoin_alternatives h.toHypothesis1221 hm,?_⟩
  refine hsource.imp fun p hp => hp.imp fun A => ?_
  iterate 11 apply And.imp_right
  exact Or.imp (D.pushingUp_core_factorization h.toHypothesis1221 hV hm
    (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1) id

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
