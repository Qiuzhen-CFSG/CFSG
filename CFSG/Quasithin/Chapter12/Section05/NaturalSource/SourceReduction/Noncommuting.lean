module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.SourceReduction.SixSpace
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.SourceReduction.ResidualFive
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.SelectionSource
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterApplicationAt
public import Theory.SpecificGroups.Alternating.FiveResidualRank

/-!
# Point escape and exterior exclusion for the original module

The unique-overgroup alternatives are excluded by the actual L₅(2)
quotient order and the nonsolvable point component. This selects an
original H-star subgroup. Under G₁ ≤ M, the Sylow omega-center has
centralizer in M. For solvable H the source module-parameter argument
places W₀ in O₂(H). For nonsolvable H, its proved A₅ residual bounds the
two-rank of H/O₂(H) by two. Apply this to every literal conjugate A of V
inside T: A intersect O₂(H) has corank at most two, strictly below
s(G,A)=3. E.3.6 and C_T(U_H)=O₂(H) again place W₀ inside O₂(H).

The actual F.7 geometry now constructs the noncommuting conjugate.
SixSpace gives the 12.4.4 point-centralizer escape; the independently
constructed terminal configuration forces the opposite containment.
Thus no exterior marking survives. Completion applies this contradiction
to the full seven-case selection. Only the genuine earlier structural and
module theorems at the same G,T remain explicit, with qt-d-1332-source
retaining their proof and final discharge.

Source: Aschbacher--Smith, 12.4.1, 12.4.4 and the end of 12.5.1,
printed pp.812--813,821--822.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
open Section04.SLThreeCommutatorSource.ConjugateExistence
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)
include s

omit [Finite G] in
theorem point_mem_sylow_omega : s.marking.z ∈ sylowCenterSeed T := by
  let := D.elementary
  rw [sylowCenterSeed_eq]
  refine (mem_omegaCenterIn_iff _ _).mpr ⟨D.le_sylow s.marking.z_mem,?_,
    elemPow_eq_one_of_isElementaryAbelian _ s.marking.z_mem⟩
  intro t ht
  exact mem_centralizer_singleton_iff.mp (s.sylow_centralizes_z ht)

omit [Finite G] in
theorem sylow_omega_centralizer_le_M
    (hpoint : s.marking.Gi 1 ≤ s.marking.M) :
    centralizer (sylowCenterSeed T : Set G) ≤ s.marking.M := by
  apply le_trans (centralizer_le (show ({s.marking.z} : Set G) ⊆ sylowCenterSeed T from
    Set.singleton_subset_iff.mpr s.point_mem_sylow_omega))
  rw [←s.marking.Gi_one_eq_centralizer]
  exact hpoint

private theorem not_unique_overgroup_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hproper : s.marking.M ≠ ⊤) : ¬ ClassificationModels.IsTheorem211Model G := by
  have hMns : ¬ Group.IsSolvable s.marking.M := by
    intro hs
    let : Group.IsSolvable (normalizer (L : Set G)) := hs
    exact Chapter1.mem_L_not_isSolvable h.maximal_faithful.1.1
      (Group.isSolvable_of_isSolvable_injective
        (f := inclusion L.le_normalizer) (inclusion_injective _))
  have hpointns : ¬ Group.IsSolvable (centralizer ({s.marking.z} : Set G)) := by
    intro hs
    let := hs
    have hi : s.marking.Li 1 ≤ centralizer ({s.marking.z} : Set G) := by
      rw [←s.marking.Gi_one_eq_centralizer]
      exact s.marking.Li_le_Gi 1
    exact Chapter1.mem_L_not_isSolvable (s.Li_mem_local 1 (.inl rfl))
      (Group.isSolvable_of_isSolvable_injective
        (f := inclusion hi) (inclusion_injective hi))
  have hcard : 9999360 ∣ Nat.card G := by
    have hc : Nat.card (L ⧸ pCore 2 L) = 9999360 :=
      (Nat.card_congr s.marking.quotientEquiv.toEquiv).trans
        Representation.SL5ExteriorSquare.card_specialLinearFive
    rw [←hc]
    exact (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 L))
      (QuotientGroup.mk'_surjective _)).trans L.card_subgroup_dvd_card
  intro hm
  cases hm with
  | bender hb =>
    exact hMns (ChapterA.Section03.SourceEmbeddings.bender_solvable_proper_sylow_overgroup
      hb T s.marking.M D.sylow_normalizes_component hproper)
  | linear_prime p hp hlarge iso =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := iso
    have ho : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
      ⟨p,1,hp.1,hp.1.odd_of_ne_two (by omega),by omega,by simpa using hF⟩
    let := D.elementary
    have hze : GorensteinWalter.IsInvolution (e s.marking.z) := by
      exact ⟨fun he => s.marking.z_ne_one (e.injective (he.trans e.map_one.symm)),by
        rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian _ s.marking.z_mem,map_one]⟩
    let := Theory.PSL2.involution_centralizer_isSolvable ho (e s.marking.z) hze
    let c := CentralizerSmallKernelTransport.centralizerEquiv e s.marking.z
    exact hpointns (Group.isSolvable_of_isSolvable_injective (f := c.toMonoidHom) c.injective)
  | linear_three iso =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := iso
    let := Fintype.ofFinite F
    let eF : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    have hc : Nat.card G = 5616 :=
      (Nat.card_congr (e.trans (Atlas.fieldEquivPSL 3 eF)).toEquiv).trans
        Matrix.PSL3Three.card_PSL
    rw [hc] at hcard
    norm_num at hcard
  | mathieu_eleven iso =>
    obtain ⟨e⟩ := iso
    have hc : Nat.card G = 7920 :=
      (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m11_order
    rw [hc] at hcard
    norm_num at hcard

theorem hasMaximalOutside_exterior
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    Chapter3.HasMaximalOutside T s.marking.M := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    h.simpleQTKE T h.maximal_faithful.1
  have hmax : IsMaximalTwoLocal s.marking.M := by
    simpa only [D.localOrbit_eq, ExteriorMarking.M] using hu.normalizer_maximal
  have hproper : s.marking.M ≠ ⊤ := by
    simpa only [D.localOrbit_eq, ExteriorMarking.M] using hu.normalizer_proper
  by_contra hout
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      (T : Subgroup G) ≤ N → N = s.marking.M := by
    intro N hN hTN
    apply hN.eq_of_le hmax.1
    by_contra hNM
    have hneq : N ≠ s.marking.M := by
      intro he
      exact hNM he.le
    exact hout (Chapter3.hasMaximalOutside_of_two_distinct hmax hN
      D.sylow_normalizes_component hTN hneq)
  exact s.not_unique_overgroup_model h hproper
    (Chapter2.theorem_2_1_1 h.simpleQTKE T _ hmax D.sylow_normalizes_component huniq)

theorem exists_HStar_exterior
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M :=
  Chapter3.exists_HStar_of_hasMaximalOutside (s.hasMaximalOutside_exterior h)

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource

namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
open Section04.SLThreeCommutatorSource.ConjugateExistence
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem core_corank_le_two {A H : Subgroup G} [IsElementaryAbelian 2 A]
    (hAH : A ≤ H) (hr : primeRank 2 (H ⧸ pCore 2 H) ≤ 2) :
    subgroupCorank A (A ⊓ H.pCoreIn 2) ≤ 2 := by
  let I := (A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
  let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.map _
  have he : subgroupCorank A (A ⊓ H.pCoreIn 2) = Nat.log 2 (Nat.card I) := by
    unfold subgroupCorank
    congr 1
    rw [inf_relIndex_left, ← relIndex_ker, QuotientGroup.ker_mk']
    have hcore : (H.pCoreIn 2).subgroupOf H = pCore 2 H :=
      comap_map_eq_self_of_injective H.subtype_injective _
    rw [← hcore, relIndex_subgroupOf hAH]
  have hI : Nat.log 2 (Nat.card I) ≤ primeRank 2 I := by
    let : IsElementaryAbelian 2 (⊤ : Subgroup I) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup I).subtype Subtype.val_injective
    simpa only [Representation.BinaryOffender.rank, Subgroup.card_top] using
      (offender_rank_le_primeRank (⊤ : Subgroup I))
  exact he.trans_le (hI.trans ((Theory.GroupTheory.primeRank_le_of_injective 2 I.subtype
    I.subtype_injective).trans hr))

private theorem weakClosure_core_of_rank_two
    {T : Sylow 2 G} {L V H : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    [IsElementaryAbelian 2 V] (hs : 2 < globalS V)
    (hr : primeRank 2 (H ⧸ pCore 2 H) ≤ 2) :
    indexedWeakClosure V (T : Subgroup G) 0 ≤ H.pCoreIn 2 := by
  let U := localModule T H
  let : IsElementaryAbelian 2 U := localModule_elementary h hH
  have hcore : (T : Subgroup G) ⊓ centralizer (U : Set G) ≤ H.pCoreIn 2 :=
    (localModule_sylow_centralizer_eq_core h (structural L h).1 hZ hH).le
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  obtain ⟨g,rfl,hg⟩ := (mem_gamma_zero_iff V (T : Subgroup G) A).mp hA
  let A := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAH : A ≤ H := hg.trans hH.1.1.2
  have hcor : (subgroupCorank A (A ⊓ H.pCoreIn 2) : ℕ∞) < globalS A := by
    have hc := core_corank_le_two hAH hr
    rw [show globalS A = globalS V from globalS_map_equiv V (MulAut.conj g)]
    exact lt_of_le_of_lt (by exact_mod_cast hc) hs
  have heq := centralizer_inf_eq_of_corank_lt_globalS inf_le_left hcor
    (IsElementaryAbelian.isPGroup 2 U)
  have hUB : U ≤ centralizer ((A ⊓ H.pCoreIn 2 : Subgroup G) : Set G) := by
    apply le_centralizer_iff.mpr
    exact inf_le_right.trans (localModule_core_centralizes h hH)
  have hUA : U ≤ centralizer (A : Set G) := by
    have hh : U ≤ U ⊓ centralizer ((A ⊓ H.pCoreIn 2 : Subgroup G) : Set G) := le_inf le_rfl hUB
    rw [heq] at hh
    exact hh.trans inf_le_right
  exact (le_inf hg (le_centralizer_iff.mp hUA)).trans hcore

namespace SylowExteriorMarking
variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
  (s : SylowExteriorMarking D)
include s

/-- The original local geometry supplies a noncommuting conjugate. The
nonsolvable H-star case uses its actual A₅ residual and s(G,V)=3. -/
theorem noncommuting_pair_from_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hpoint : s.marking.Gi 1 ≤ s.marking.M) :
    ∃ g : G, ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  let := D.elementary
  have hZ := s.sylow_omega_centralizer_le_M hpoint
  have hs : globalS V = 3 := (s.exteriorFusion_from_source h structural).parameters.2.2
  obtain ⟨H,hH⟩ := s.exists_HStar_exterior h
  by_cases hsolv : Group.IsSolvable H
  · let := localModule_elementary h hH
    apply noncommutingConjugate_of_hstar_parameter_at h D structural hZ hH
      (localModule_parameter_of_solvable h hH hsolv)
    rw [hs]
    norm_num
  obtain ⟨e⟩ := SourcePointEscape.hstar_residual_five h structural modules hZ hH hsolv
  have hr := Theory.SpecificGroups.Alternating.FiveExtensionAction.twoCoreQuotient_rank_le_two_of_residual_five e
  have hW := weakClosure_core_of_rank_two h structural hZ hH (by rw [hs]; norm_num) hr
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hHM : ¬ H ≤ normalizer (L : Set G) := hH.1.2
  let A := localGeometryAt h D structural hTH hHM
  let J := L ⊔ (T : Subgroup G) ⊔ H
  have hseed : A.seed.map J.subtype = V := localGeometryAt_seed_map h D structural hTH hHM
  have hsyl : ((A.sylow false : Subgroup (localFamily T L H false)).map
      (localFamily T L H false).subtype).map J.subtype = (T : Subgroup G) :=
    localGeometryAt_sylow_map h D structural hTH hHM
  have hsecond : (localFamily T L H true).map J.subtype = H :=
    map_subgroupOf_eq_of_le le_sup_right
  have hw : indexedWeakClosure (A.seed.map J.subtype)
      (((A.sylow false : Subgroup (localFamily T L H false)).map
        (localFamily T L H false).subtype).map J.subtype) 0 ≤
      ((localFamily T L H true).map J.subtype).pCoreIn 2 := by
    rw [hseed,hsyl,hsecond]
    exact hW
  have hc := exists_ambient_conjugate_of_weakClosure_core A
    (localGeometryAt_ne_bot h D structural hTH hHM) J.subtype J.subtype_injective hw
  rwa [hseed] at hc

/-- The point-centralizer escape in the exterior case of 12.4.4. -/
theorem point_group_not_le_M_from_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T) :
    ¬ s.marking.Gi 1 ≤ s.marking.M := by
  intro hpoint
  obtain ⟨g,hne,hle⟩ := s.noncommuting_pair_from_source h structural modules hpoint
  exact s.noncommuting_pair_excluded h structural hpoint g hne hle

/-- The exterior-square branch is impossible under the original source
hypotheses and the earlier same-G,T structural and module theorems. -/
theorem exterior_false_from_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T) : False := by
  exact s.point_group_not_le_M_from_source h structural modules
    (s.point_group_le_M_from_terminal h structural)

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
