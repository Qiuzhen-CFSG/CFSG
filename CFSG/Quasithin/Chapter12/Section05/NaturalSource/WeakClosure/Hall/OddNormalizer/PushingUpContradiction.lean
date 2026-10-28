module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpRadicalSplit
public import Theory.GroupAction.FixedInvolutionDirectFactor
/-!
# The original exterior pushing-up contradiction

The full J₄ covering quotient bounds the binary radical intersection by the
original 1024-element exterior module. Thus the radical splits as V times
its nontrivial component centralizer, retaining the covering center in the
second factor. The binary normalizer fixes modulo V an actual central
involution in that factor. Reselect a maximal two-local over its centralizer;
the same full J₄ component remains normal there. At the original cubic, the
commutator image and actual fixed lift now force the enlarged binary
normalizer to centralize that involution. Relative Sylow maximality then
contradicts its strict containment of the original radical.

This completes the exterior specialization of the p.612 branch. The distinct
odd-local comparison on p.623 remains with OddNormalizer's Hall assembly.
Source: Aschbacher--Smith, Theorem 4.2.13, printed p.612.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Subgroup Theory.GroupTheory
open Chapter4 Chapter4.Section04 Chapter12.Section02
open Chapter4.Section02.RankOneReciprocalEscape
open scoped Pointwise commutatorElement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The p.612 contradiction at the original exterior cubic. Choose an
actual involution in the split centralizer factor fixed modulo V by R₁,
reselect an overgroup of its full centralizer, and retain the full J₄ cover.
The commutator fixed-lift argument then contradicts R < R₁. -/
theorem exterior_pushingUp_fixed_involution_contradiction
    (s : SylowExteriorMarking D) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K) (e : (K ⧸ center K) ≃* Janko4.Model)
    (hout : ¬ K ≤ (H ⊓ s.marking.M).subgroupOf H)
    (k : K) (hk : orderOf k = 3)
    (hkF : ((k : H) : G) ∈ (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
    (hfix : 16 ≤ Nat.card (V ⊓ centralizer ({((k : H) : G)} : Set G) : Subgroup G)) : False := by
  let R := J.pCoreIn 2
  let Kg := K.map H.subtype
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let I := F ⊔ R
  let M := normalizer (L : Set G)
  let hc := hw.2.2.2.2.2.2.1
  have hFK : F ≤ Kg := by
    have hh := map_mono (f := H.subtype) (hc.ordinary_component_contains_original K hK)
    rwa [map_subgroupOf_eq_of_le ((map_subtype_le _).trans inf_le_right)] at hh
  obtain ⟨c,hPc,hPsec,hgen,hlt,hPH,hlt₁,hQ,hFQ⟩ := exterior_pushingUp_source_normalizer s h hw
  let P := (L ⊔ (((c : G) • T : Sylow 2 G) : Subgroup G)).pCoreIn 2
  let Q := P ⊓ normalizer (R : Set G)
  have hPC : P ≤ sectionCentralizerIn s.marking.M L := by
    change (L ⊔ (((c : G) • T : Sylow 2 G) : Subgroup G)).pCoreIn 2 ≤ _
    rw [hPsec]
    intro p hp
    exact ⟨((le_sectionCentralizer_iff (sectionCentralizer L) L).mp le_rfl).1 hp.2,hp.2⟩
  have hPV := exterior_pushingUp_signalizer_centralizes s h hw
    (isPGroup_pCoreIn 2 _) hPC hlt.le
  have hQV : Q ≤ centralizer (V : Set G) := inf_le_left.trans hPV
  obtain ⟨hs,hd,hne,hVC⟩ := exterior_pushingUp_radical_module_split s hw K hK e
  obtain ⟨r,hr,ho,hrR,hcomm⟩ := exists_central_involution_fixed_modulo_direct_factor
    R V (R ⊓ centralizer (Kg : Set G)) Q (isPGroup_pCoreIn 2 J) hQ
      D.elementary hs hd hVC hne inf_le_right hQV
  have hKC : Kg ≤ centralizer ({r} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hr.2 a ha)
  have hRC : R ≤ centralizer ({r} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hrR a ha)
  have hIC : I ≤ centralizer ({r} : Set G) := sup_le (hFK.trans hKC) hRC
  have hlocal : IsTwoLocal (centralizer ({r} : Set G)) := by
    refine ⟨zpowers r,?_,?_,(normalizer_zpowers_eq_centralizer_of_order_two r ho).symm⟩
    · intro hb
      have hh := mem_zpowers r
      rw [hb,mem_bot] at hh
      rw [hh,orderOf_one] at ho
      omega
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,ho,pow_one])
  obtain ⟨H',hH',hCH'⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
    (centralizer ({r} : Set G)) (by
      intro hb
      exact (Chapter1.mem_H_of_isTwoLocal hlocal)
        (by simp only [pCoreIn,hb,Subgroup.map_bot]))
  have hKH' : Kg ≤ H' := hKC.trans hCH'
  have hHout : ¬ H' ≤ M := by
    intro hm
    apply hout
    intro a ha
    exact ⟨a.property,hm (hKH' (mem_map_of_mem H.subtype ha))⟩
  have hM := exterior_component_sylow_unique s h
  obtain ⟨hcore,hpush,_,hI⟩ := residual_core_selection h.toHypothesis1221 D hM hw
  obtain ⟨W',hw'⟩ := witness_on_selected_overgroup h.toHypothesis1221 D hM hw
    hpush hI hH' (hIC.trans hCH') hHout
  obtain ⟨hK',hn'⟩ := exterior_pushingUp_component_in_reselected_overgroup s h hw' K hK e hKH'
  have hKN : (Kg.subgroupOf (centralizer ({r} : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer (hCH'.trans
      ((normal_subgroupOf_iff_le_normalizer hKH').mp hn'))
  have hvanish : Q ≤ centralizer ({r} : Set G) :=
    exterior_pushingUp_cubic_commutator_vanishes s h hw K hK
      (hc.ordinary_component_normal K hK) e k hk hkF hfix r ho hKC hKN Q hQ
      (le_centralizer_iff.mp hQV) hFQ hcomm
  have hm : coveringOvergroup M L (oddActorResidual L A) ∈ sigma M L := by
    refine ⟨sup_le (((oddActorResidual_le L A).trans inf_le_left).trans L.le_normalizer)
      inf_le_left,sup_le ?_ le_sup_right⟩
    intro l hl
    obtain ⟨j,hj,q,hq,rfl⟩ := hw.1.1.1.2.2.1 hl
    exact mul_mem (hw.1.1.1.1 hj)
      (show q ∈ coveringOvergroup M L (oddActorResidual L A) from
        (show sectionCentralizerIn M L ≤ coveringOvergroup M L (oddActorResidual L A) from le_sup_right)
          (componentCore_le_sectionCentralizer L.le_normalizer hq))
  obtain ⟨S,hS⟩ := core_sylow_sectionCentralizer_outside
    (source_hypothesis411 h.toHypothesis1221 hM) hm hI
    (Chapter1.mem_H_of_isTwoLocal hH'.1) (hIC.trans hCH') hHout
  rw [hcore] at hS
  have hmax := Chapter1.isSylowIn_iff.mp (show Chapter1.IsSylowIn 2 R
    (sectionCentralizerIn (H' ⊓ M) L) from ⟨S,hS⟩)
  have hQR : Q = R := hmax.2.2 Q hQ hlt₁.le (by
    intro q hq
    exact ⟨⟨hCH' (hvanish hq),(hPC hq.1).1⟩,(hPC hq.1).2⟩)
  exact hlt₁.ne hQR.symm

/-- The complete original pushing-up branch is impossible. -/
theorem exterior_pushingUp_module_control_false
    (s : SylowExteriorMarking D) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A : Subgroup G} (hj : ExteriorPushingUpModuleControlCase s A) : False := by
  obtain ⟨J,H,W,hw,_,_,_,K,hK,_,hout,_,_,_,⟨e⟩,_,x,k,hkx,_,hk,hfix,_⟩ := hj
  apply exterior_pushingUp_fixed_involution_contradiction s h hw K hK e hout k hk
    (by rw [hkx]; exact x.property)
  simpa only [hkx] using hfix

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
