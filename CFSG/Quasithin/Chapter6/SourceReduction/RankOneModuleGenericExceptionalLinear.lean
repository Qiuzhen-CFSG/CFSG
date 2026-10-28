module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalGeometry
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Centralizing
public import Theory.GroupTheory.ReducedNormal.SylowCenter

/-!
# The nonfaithful residual step in the exceptional linear case

The first paragraph of 5.1.14 proves that the actual residual K is maximal
in L(G,T) and is not in X_f. From these earlier assertions, A.4.8 puts
[R₂(H),K] in the zero intrinsic module of K, and B.2.14 puts Ω₁(Z(T))
inside R₂(H). Thus K and H centralize Ω₁(Z(T)). The genuine 1.2.7 then
identifies every maximal two-local over H with N_G(K).

All subgroup maps here are the original inclusions into H and G. The
maximality and nonfaithfulness assertions still require the L₃(4) analysis
of 5.1.10, 5.1.12 and 3.2.3--9. They are explicit premises, not conclusions
claimed by this module. No module classification on L is used.
Source: Aschbacher--Smith, 5.1.14(1--2), printed pp.638--639.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {H : Subgroup G}

/-- The original PSL₃(4) quotient makes O²(H) a relative C-component.
Together with KT=H, this already proves canonical local-family membership;
only maximality in that family needs the further embedding analysis. -/
theorem linear_residual_mem_localFamily
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    residual H ∈ Chapter1.L G (T : Subgroup G) := by
  have hTH : (T : Subgroup G) ≤ H := hH.2
  obtain ⟨F, _, _, _, ⟨f⟩⟩ := hlinear
  let : IsQuasisimple ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) :=
    IsQuasisimple.of_mulEquiv f.symm
  have hRH : residual H ≤ H := map_subtype_le _
  let e := ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
    (subgroupOfEquivOfLe hRH).symm
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let : IsQuasisimple (((residual H).subgroupOf H) ⧸ pCore 2 ((residual H).subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv q
  have hn : ((residual H).subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_residual H)
  have hc := isCComponent_of_isPPerfect_of_quasisimple_core_quotient hn.isSubnormal
    ((isPPerfect_pResidual 2).of_surjective e.toMonoidHom e.surjective)
  change ((residual H).subgroupOf (residual H ⊔ (T : Subgroup G))).IsCComponent ∧ _
  rw [residual_sup_sylow T H hTH]
  refine ⟨hc, ⟨T.subtype hTH, ?_⟩, hH.1⟩
  simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]

/-- Vanishing of the intrinsic module makes the embedded residual centralize
the actual Sylow omega-center. The characteristic-two hypothesis is on H. -/
theorem residual_centralizes_omega_of_intrinsic_eq_bot
    (hTH : (T : Subgroup G) ≤ H)
    (hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hzero : intrinsicSignalizerModule (residual H) = ⊥) :
    residual H ≤ omegaCentralizer T := by
  let R := (reducedTwoSubgroup H).map H.subtype
  have hc : ⁅R, residual H⁆ = ⊥ := by
    apply le_bot_iff.mp
    have hh := map_mono (reduced_commutator_le_intrinsicModule
      (pResidual 2 H) (Subgroup.Normal.isSubnormal inferInstance)
      (isPPerfect_pResidual 2)) (f := H.subtype)
    rw [map_commutator, ← intrinsicSignalizerModule_map_of_injective
      H.subtype H.subtype_injective, hzero] at hh
    exact hh
  have hZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤ R := by
    have hz := map_mono (sylow_omegaCenter_le_reduced (T.subtype hTH) hchar)
      (f := H.subtype)
    change (Stellmacher.omegaOneCenterAmbient
      ((T.subtype hTH : Sylow 2 H) : Subgroup H)).map H.subtype ≤ R at hz
    rw [← Stellmacher.omegaOneCenterAmbient_map_injective H.subtype
      H.subtype_injective, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at hz
    exact hz
  exact le_centralizer_iff.mp
    (hZ.trans (commutator_eq_bot_iff_le_centralizer.mp hc))

/-- The source nonfaithfulness assertion suffices because canonical local
components already belong to X by characteristic two. -/
theorem residual_centralizes_omega_of_nonfaithful
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hK : residual H ∈ Chapter1.L G (T : Subgroup G))
    (hnf : ¬ IsFaithfulSignalizerType (residual H)) :
    residual H ≤ omegaCentralizer T := by
  have hs := Chapter1.Section02.Adequate.mem_L_isSignalizerType
    T (hG.evenCharacteristic T) hK
  have hz : intrinsicSignalizerModule (residual H) = ⊥ := by
    by_contra hn
    exact hnf ⟨hs, hn⟩
  exact residual_centralizes_omega_of_intrinsic_eq_bot hH.2
    (Chapter1.mem_He_iff.mp
      (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hH)) hz

/-- For the literal residual, the orbit in 1.2.7 equals K itself and KT=H.
Consequently maximality in the canonical local family gives the exact source
normalizer, with no ambient normality assumption. -/
theorem residual_unique_of_maximal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTH : (T : Subgroup G) ≤ H)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G)) :
    ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N →
      N = normalizer (residual H : Set G) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple hG T hK
  have he : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      (hTH.trans (le_normalizer_residual H))) (le_componentOrbit _ _)
  intro N hN hHN
  have hh := hu.normalizer_unique N hN
    ((residual_sup_sylow T H hTH).le.trans hHN)
  simpa only [he] using hh

/-- The two geometric conclusions of 5.1.14 follow from its preceding
maximality and nonfaithfulness assertions on the actual residual. -/
theorem residual_geometry_of_maximal_nonfaithful
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ IsFaithfulSignalizerType (residual H)) :
    residual H ≤ omegaCentralizer T ∧
      ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N →
        N = normalizer (residual H : Set G) :=
  ⟨residual_centralizes_omega_of_nonfaithful hG hH hK.1 hnf,
    residual_unique_of_maximal hG hH.2 hK⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
