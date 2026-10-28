module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryInnerPlacement
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FiveInteriorExtension
public import Theory.GroupTheory.ReducedNormal.QuasisimpleKernel
public import Theory.GroupTheory.ReducedNormal.CentralSeedClosure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AutomorphismNoFF

/-!
# Completion of the constrained degree-five linear branch

The interior flag has the actual GL₃(2) two-core quotient. In the graph
branch its Sylow extension has Aut(GL₃(2)) quotient: graph exchange of
its two nodes excludes the inner extension. The original central-involution
seed has a reduced orbit span in this characteristic-two extension.

If the interior centralizes the seed, the singleton centralizer overgroup
places it in M_Z. Otherwise its action on that reduced span is faithful
modulo the extension's two-core. The proved Aut(GL₃(2)) FF exclusion forces
J(S) into this core. Thompson heredity and the original normalizer control
then place the interior in M. The already placed endpoint and this interior
generate L, so both original intersections generate L.

Combined with the checked inner branch this proves the full degree-five
linear ConstrainedAlternatives conclusion for either original source prime,
retaining the original quotient marking. The exchanged source also consumes
the same interior quotient and placement on both plane sizes. Original
15.1.14 remains explicit for its existing producer and final assembly owner.
The degree-four graph branch, small blocks and general Borel placement
remain obligations of this catalogue.

Source: Aschbacher--Smith 15.1.22(3), printed pp.1099--1100, using B.2.3(3),
B.2.7, B.2.14, B.5.1 and 15.1.17.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

/-- The marked interior retains its actual three-dimensional Levi quotient. -/
theorem BinaryNodeGeometry.five_interior_quotient
    {d : CaseIComponentData T M Mc V}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(4+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a) :
    Nonempty ((a.interior ⧸ pCore 2 a.interior) ≃* LinearGroup 3) := by
  let q := coreFlagMap d.L e
  let P := a.interior.subgroupOf d.L
  let C := cutStabilizer b.basis {i : Fin 4 | i.val=0 ∨ i.val=3}
  have hi : P.map q = C := by
    change (a.interior.subgroupOf d.L).map q = C
    rw [b.interior_marking]
    exact coreFlagMap_lift_image d.L e C
  let t : P ≃* a.interior := subgroupOfEquivOfLe a.interior_proper.le
  let f : a.interior →* C := ((MulEquiv.subgroupCongr hi).toMonoidHom.comp
    (q.subgroupMap P)).comp t.symm.toMonoidHom
  have hf : Function.Surjective f := (MulEquiv.subgroupCongr hi).surjective.comp
    ((q.subgroupMap_surjective P).comp t.symm.surjective)
  have hk : f.ker = (q.ker.subgroupOf P).comap t.symm.toMonoidHom := by
    ext x
    change (⟨q (t.symm x : d.L),_⟩ : C) = 1 ↔ q (t.symm x : d.L) = 1
    exact Subtype.ext_iff
  have hker : IsPGroup 2 f.ker := by
    rw [hk,show q.ker = pCore 2 d.L from coreFlagMap_ker d.L e]
    exact pCore_isPGroup.comap_subtype.comap_of_injective _ t.symm.injective
  obtain ⟨u⟩ := BinaryLinear.InvariantNodeActions.five_interior_quotient b.basis
  exact ⟨(f.pCoreQuotientEquiv hf hker).trans u⟩

/-- The actual interior Sylow extension has the full automorphism quotient
whenever the original action contains a graph actor. -/
theorem BinaryNodeGeometry.five_graph_interior_quotient
    {d : CaseIComponentData T M Mc V}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(4+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S)
    (ho : ∃ x : d.S, coreFlagAction d.L d.S b.normalizes e x ∉ MulAut.innerSubgroup _) :
    Nonempty (((a.interior ⊔ d.S : Subgroup G) ⧸
      pCore 2 (a.interior ⊔ d.S : Subgroup G)) ≃* MulAut (LinearGroup 3)) := by
  obtain ⟨Q,hQ⟩ := ComponentModels.source20_sylow_intersection hK.2
  obtain ⟨u⟩ := b.five_interior_quotient
  exact five_interior_extension_aut d.L d.S b.normalizes (T.isPGroup'.to_le d.S_le_T)
    Q hQ e b.basis b.sylow_image a.interior b.interior_marking a.normalizes_interior u ho

private theorem linear_three_center : center (LinearGroup 3) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hz := (centerCongr (slEquivLinear 3).symm ⟨x,hx⟩).property
  have he : (slEquivLinear 3).symm x = 1 := Matrix.PSL3Two.center_eq_bot.le hz
  exact (slEquivLinear 3).symm.map_eq_one_iff.mp he

private theorem linear_three_quasisimple : IsQuasisimple (LinearGroup 3) := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup (LinearGroup 3) := (projectiveEquivLinear (by decide : 0 < 3)).symm.isSimpleGroup
  exact { toIsPerfect := BinaryLinear.linearGroup_isPerfect 3 (by decide)
          simple := ((QuotientGroup.quotientMulEquivOfEq linear_three_center).trans
            QuotientGroup.quotientBot).isSimpleGroup }

private theorem reduced_aut_thompson
    {H : Type*} [Group H] [Finite H]
    (W K : Subgroup H) [W.Normal] [K.Normal]
    (hr : IsPReduced 2 W) (hm : ⁅W,K⁆ ≠ ⊥)
    (eK : (K ⧸ pCore 2 K) ≃* LinearGroup 3)
    (hquot : IsPGroup 2 (H ⧸ K))
    (eH : (H ⧸ pCore 2 H) ≃* MulAut (LinearGroup 3)) (P : Sylow 2 H) :
    elementaryAbelianMaxJ (P : Subgroup H) ≤ pCore 2 H := by
  let := linear_three_quasisimple
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv eK.symm
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hy := (centerCongr eK ⟨x,hx⟩).property
    exact eK.map_eq_one_iff.mp (linear_three_center.le hy)
  have hC := reduced_quasisimple_centralizer_eq_pCore W K hr hz hm hquot
  let := hr.elementary
  let q := eH.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := eH.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = centralizer (W : Set H) := by
    rw [MonoidHom.ker_comp_of_injective _ _ eH.injective,QuotientGroup.ker_mk',hC]
  by_contra hn
  have hnot : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ q.ker := by rwa [hk,hC]
  have hff := (ChapterB.lemma_B_2_7_local W q hq hk P
    (hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal P)) hnot).1
  exact ChapterC.BinaryMS.AutomorphismNoFF.not_isFFModule_linear_of_faithful
    (NormalElementaryQuotient.representation W q hq hk)
    (NormalElementaryQuotient.representation_injective W q hq hk) hff

/-- The full graph-extension FF obstruction places the actual interior in
one of the two original intersections, retaining the original central seed. -/
theorem BinaryNodeGeometry.five_graph_interior_placement
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(4+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (ho : ∃ x : d.S, coreFlagAction d.L d.S b.normalizes e x ∉ MulAut.innerSubgroup _) :
    a.interior ≤ M ⊓ d.L ∨ a.interior ≤ d.ML := by
  let C := a.interior
  by_cases hc : C ≤ centralizer (centralInvolutions T : Set G)
  · right
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    exact le_inf (le_inf (a.interior_proper.le.trans d.L_component.1) (hc.trans hMc.2)) a.interior_proper.le
  · left
    let H := C ⊔ d.S
    let K := C.subgroupOf H
    let Z := (centralInvolutions T).subgroupOf H
    let W := normalClosure (Z : Set H)
    let : K.Normal := normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer a.normalizes_interior)
    obtain ⟨Q,hQ⟩ := ComponentModels.source20_sylow_intersection hK.2
    have hQC : (Q : Subgroup d.L) ≤ C.subgroupOf d.L := by
      intro x hx
      have hxSL : (x : G) ∈ d.S ⊓ d.L := hQ ▸ mem_map_of_mem d.L.subtype hx
      exact a.sylow_interior hxSL
    let t : C.subgroupOf d.L ≃* C := subgroupOfEquivOfLe a.interior_proper.le
    let R := (Q.subtype hQC).mapSurjective (f := t.toMonoidHom) t.surjective
    have hRS : (R : Subgroup C).map C.subtype ≤ d.S := by
      rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
      exact (hQ ▸ mem_map_of_mem d.L.subtype hz).1
    obtain ⟨P,hP⟩ := IsPGroup.exists_sylow_sup_of_coprime_index C d.S
      (T.isPGroup'.to_le d.S_le_T) a.normalizes_interior (R : Subgroup C) R.not_dvd_index hRS
    have hPS : (P : Subgroup H) = d.S.subgroupOf H := by
      apply map_injective H.subtype_injective
      rw [hP,map_subgroupOf_eq_of_le (show d.S ≤ H from le_sup_right)]
    have hZS : centralInvolutions T ≤ d.S := le_inf (centralInvolutions_le_sylow T)
      ((centralInvolutions_le_centralizer_sylow T).trans (centralizer_le (d.marked_le_sylow h hM.1.2)))
    let : IsElementaryAbelian 2 (centralInvolutions T) := by
      change IsElementaryAbelian 2 (omegaCenterIn (T : Subgroup G)); infer_instance
    let : IsElementaryAbelian 2 Z := IsElementaryAbelian.subgroupOf (hZS.trans le_sup_right)
    have hZP : Z ≤ P := by rw [hPS]; exact fun _ hz => hZS hz
    have hZC : Z ≤ centralizer (P : Set H) := by
      intro z hz x hx
      exact Subtype.ext (centralInvolutions_le_centralizer_sylow T hz x
        (d.S_le_T (hP ▸ mem_map_of_mem H.subtype hx)))
    have hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
      centralizer_pCore_sup_le 2 C d.S
        (a.interior_fitting ▸ centralizer_generalizedFitting_le C)
        (T.isPGroup'.to_le d.S_le_T) a.normalizes_interior
    have hr : IsPReduced 2 W := centralSeed_normalClosure_reduced P Z hZP hZC hchar
    have hm : ⁅W,K⁆ ≠ ⊥ := by
      intro he
      have hh := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
      apply hc
      intro x hx z hz
      exact congrArg Subtype.val (hh (show (⟨x,mem_sup_left hx⟩ : H) ∈ K from hx)
        ⟨z,mem_sup_right (hZS hz)⟩ (le_normalClosure hz))
    let u : K ≃* C := subgroupOfEquivOfLe le_sup_left
    obtain ⟨eC⟩ := b.five_interior_quotient
    let eK := (QuotientGroup.congr _ _ u (pCore_map_iso 2 u)).trans eC
    have hquot : IsPGroup 2 (H ⧸ K) := by
      let q := QuotientGroup.mk' K
      have hgen : K ⊔ (P : Subgroup H) = ⊤ := by
        apply map_injective H.subtype_injective
        rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show C ≤ H from le_sup_left),hP,
          ←MonoidHom.range_eq_map,range_subtype]
      have him : (P : Subgroup H).map q = ⊤ := by
        have hh := congrArg (map q) hgen
        rw [Subgroup.map_sup,show K.map q = ⊥ from (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' K).ge,
          bot_sup_eq,←MonoidHom.range_eq_map,q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective _)] at hh
        exact hh
      have hp := P.isPGroup'.map q
      rw [him] at hp
      exact hp.of_equiv topEquiv
    obtain ⟨eH⟩ := b.five_graph_interior_quotient hK ho
    have hJQ := reduced_aut_thompson W K hr hm eK hquot eH P
    have hJeq := elementaryAbelianMaxJ_eq_of_intermediate (P : Subgroup H) (pCore 2 H)
      hJQ (pCore_isPGroup.le_sylow_of_normal P)
    have hn : K ≤ normalizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H) := by
      rw [←hJeq]
      exact le_normalizer_of_normal.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)
    have hn' := (map_mono (f := H.subtype) hn).trans
      ((elementaryAbelianMaxJ (P : Subgroup H)).le_normalizer_map H.subtype)
    rw [map_subgroupOf_eq_of_le (show C ≤ H from le_sup_left),
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP] at hn'
    have he := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).1
    rw [show elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ (T : Subgroup G) from he] at hn'
    exact le_inf (hn'.trans (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1)
      a.interior_proper.le


/-- Interior placement and the already placed endpoint generate the original
component in the degree-five graph branch. -/
theorem PreExclusionSource.binary_five_graph_generated
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(4+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (ho : ∃ x : d.S, coreFlagAction d.L d.S b.normalizes e x ∉ MulAut.innerSubgroup _) :
    (M ⊓ d.L) ⊔ d.ML = d.L := by
  have hC : a.interior ≤ (M ⊓ d.L) ⊔ d.ML := by
    rcases b.five_graph_interior_placement (h := h) ⟨d.L_component.1,s.local_component⟩
        hG hM hJ hu ho with hm | hm
    · exact hm.trans le_sup_left
    · exact hm.trans le_sup_right
  have hE : a.endpoint ≤ (M ⊓ d.L) ⊔ d.ML := by
    rcases (s.five_graph_endpoint_eq (h := h) hG hM hJ hu b ho).2 with he | he
    · exact he ▸ le_sup_left
    · exact he ▸ le_sup_right
  apply le_antisymm (sup_le inf_le_right inf_le_right)
  calc
    d.L = a.interior ⊔ a.endpoint := a.generated.symm
    _ ≤ (M ⊓ d.L) ⊔ d.ML := sup_le hC hE

/-- Both actions on the original degree-five FF row supply the complete
linear constrained alternative, with the literal quotient marking and
generation of the two original intersections. -/
theorem PreExclusionSource.constrained_binary_five
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* SL(5,ZMod 2)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(5,ZMod 2),
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
      (M ⊓ d.L) ⊔ d.ML = d.L ∧ d.ConstrainedAlternatives := by
  obtain ⟨t,ht,hML,hM',a,ha,⟨b⟩⟩ :=
    s.constrained_binary_nodes (h := h) hG hempty hM hJ hu hf (Or.inr rfl) e
  have hg : (M ⊓ d.L) ⊔ d.ML = d.L := by
    rcases b.action with hi | ⟨ho,_⟩
    · exact s.binary_inner_generated (h := h) hG hM hJ hu hf (by decide) b hi.1
    · exact s.binary_five_graph_generated (h := h) hG hM hJ hu b ho
  exact ⟨t,ht,hML,hM',hg,ConstrainedAlternatives.linear 5 (Or.inr rfl) t hML hM' hg⟩

/-- Later exchanged selection consumes the same graph-interior quotient and
placement on either plane size, without altering the earlier original source. -/
theorem ExchangedSource.constrained_binary_five_graph_interior
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* SL(5,ZMod 2)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(5,ZMod 2),
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
      ∃ a : d.BinaryGeneratingParabolics t, ∃ b : d.BinaryNodeGeometry a,
        (∀ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∈ MulAut.innerSubgroup _) ∨
          ((∃ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∉ MulAut.innerSubgroup _) ∧
            Nonempty (((a.interior ⊔ d.S : Subgroup G) ⧸ pCore 2 (a.interior ⊔ d.S : Subgroup G))
              ≃* MulAut (LinearGroup 3)) ∧
            (a.interior ≤ M ⊓ d.L ∨ a.interior ≤ d.ML)) := by
  obtain ⟨t,ht,hML,hM',a,ha,⟨b⟩⟩ :=
    s.constrained_binary_nodes hG hempty hM hJ hu h hf (Or.inr rfl) e
  refine ⟨t,ht,hML,hM',a,b,?_⟩
  rcases b.action with hi | ⟨ho,_⟩
  · exact Or.inl hi.1
  · exact Or.inr ⟨ho,b.five_graph_interior_quotient ⟨d.L_component.1,s.local_component⟩ ho,
      b.five_graph_interior_placement (h := h) ⟨d.L_component.1,s.local_component⟩ hG hM hJ hu ho⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open BinaryLinear.InvariantNodeActions
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original marker receives the full degree-five linear alternative for
both original primes. Original 15.1.14 remains explicit for its independent
producer and the final source assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_constrained_binary_five
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (marker : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = marker.Z1 ∧ d.row = marker.row ∧
      d.PreExclusionSource h.normalized marker.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ e : d.normalizerImage d.L ≃* SL(5,ZMod 2),
        ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(5,ZMod 2),
          (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
          d.ConstrainedLinearParabolic t d.ML ∧
          d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
          (M ⊓ d.L) ⊔ d.ML = d.L ∧ d.ConstrainedAlternatives) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull marker hres
  exact ⟨d,hZ,hr,s,fun hf e =>
    s.constrained_binary_five (h := h) hG hempty hM hJ hu hf e⟩
end CFSG.Quasithin.Chapter15.Section01
