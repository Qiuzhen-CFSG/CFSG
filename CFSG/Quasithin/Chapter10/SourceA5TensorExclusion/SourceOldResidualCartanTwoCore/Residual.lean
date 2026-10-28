module
public import Theory.SpecificGroups.Alternating.FiveSylowMaximal
public import Theory.SpecificGroups.Alternating.FiveSylowRadical
public import Theory.GroupTheory.PCoreQuotientInnerSupplement
public import Theory.GroupTheory.PCoreImage
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OldComponent
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.Borel

/-!
# The old residual side of the Cartan two-core equality

Put P = AT and K = O²(H), with the literal ambient image of the residual.
The original maximal local subgroup contains P and misses K. Since K/O₂(K)
is A₅, its unique Sylow overgroup makes T ∩ K the two-core of P ∩ K.
Consequently P normalizes T ∩ K. The marked cubic subgroup of K acts
nontrivially on the quotient, so the normal two-subgroup O₂(P) induces
inner automorphisms of K/O₂(K). The inner-action supplement theorem now
gives O₂(P) = (T ∩ K) O₂(K O₂(P)). Normality in KP identifies the latter
core with O₂(KP), and KT = H gives the required literal equality.

The actual source consumer retains the earlier A₅ recognition and Cartan
normalization conclusions. No product-order, line-action or additional
quotient-model premise is needed.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma 9.3.2, printed p.733.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.CartanCore
variable {G : Type*} [Group G] [Finite G]

private theorem proper_overgroup_normalizes {K : Type*} [Group K] [Finite K]
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 K) (J : Subgroup K) (hSJ : (S : Subgroup K) ≤ J) (hJ : J ≠ ⊤) :
    J ≤ normalizer (S : Set K) := by
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    ext k
    change eK (QuotientGroup.mk' (pCore 2 K) k) = 1 ↔ k ∈ pCore 2 K
    rw [map_eq_one_iff eK eK.injective]
    exact QuotientGroup.eq_one_iff k
  have hkS : q.ker ≤ (S : Subgroup K) := hk ▸ pCore_isPGroup.le_sylow_of_normal S
  have hJq : J.map q ≠ ⊤ := by
    intro he
    apply hJ
    have hc := congrArg (comap q) he
    simpa only [comap_map_eq, sup_eq_left.mpr (hkS.trans hSJ), comap_top] using hc
  have hn := Theory.SpecificGroups.Alternating.FiveSylowMaximal.overgroup_le_sylow_normalizer
    (S.mapSurjective hq) (J.map q) (map_mono hSJ) hJq
  have hc := (le_comap_map q J).trans (comap_mono (f := q) hn)
  change J ≤ (normalizer (((S : Subgroup K).map q) : Set _)).comap q at hc
  rw [comap_normalizer_eq_of_surjective _ hq, comap_map_eq_self hkS] at hc
  exact hc

private theorem intersection_normalizes (T : Sylow 2 G) (K P : Subgroup G)
    (hPK : P ≤ normalizer (K : Set G)) (hTP : (T : Subgroup G) ≤ P)
    (hK : ¬ K ≤ P)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    P ≤ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K (hTP.trans hPK)
  let J := P.subgroupOf K
  have hSJ : (S : Subgroup K) ≤ J := by rw [hS]; exact comap_mono hTP
  have hJ : J ≠ ⊤ := by
    intro he
    apply hK
    intro k hk
    exact (show (⟨k,hk⟩ : K) ∈ J from he ▸ mem_top _)
  have hJN := proper_overgroup_normalizes eK S J hSJ hJ
  have hcore : J.pCoreIn 2 = (S : Subgroup K) := by
    apply le_antisymm
    · have hh := pCoreIn_le_sylow J (S.subtype hSJ)
      change J.pCoreIn 2 ≤ ((S : Subgroup K).subgroupOf J).map J.subtype at hh
      rwa [map_subgroupOf_eq_of_le hSJ] at hh
    · exact le_pCoreIn_of_normalizes S.isPGroup' hSJ hJN
  have he : (P ⊓ K : Subgroup G).pCoreIn 2 = (T : Subgroup G) ⊓ K := by
    have hh := congrArg (map K.subtype) hcore
    rw [map_pCoreIn_of_injective 2 _ _ K.subtype_injective, subgroupOf_map_subtype,
      hS, subgroupOf_map_subtype] at hh
    exact hh
  have hPC : P ≤ normalizer ((P ⊓ K : Subgroup G) : Set G) :=
    (le_inf P.le_normalizer hPK).trans inf_normalizer_le_normalizer_inf
  rw [←he]
  exact hPC.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 (P ⊓ K : Subgroup G)))

private theorem core_factor (T : Sylow 2 G) (K P B : Subgroup G)
    (hPK : P ≤ normalizer (K : Set G)) (hTP : (T : Subgroup G) ≤ P)
    (hK : ¬ K ≤ P) (hBP : B ≤ P) (hBK : B ≤ K) (hB3 : Nat.card B = 3)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    P.pCoreIn 2 = ((T : Subgroup G) ⊓ K) ⊔ (K ⊔ P).pCoreIn 2 := by
  have hPTS := intersection_normalizes T K P hPK hTP hK eK
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K (hTP.trans hPK)
  have hSm : (S : Subgroup K).map K.subtype = (T : Subgroup G) ⊓ K := by
    rw [hS,subgroupOf_map_subtype]
  let R := P.pCoreIn 2
  have hRP : R ≤ P := P.pCoreIn_le 2
  have hRK : R ≤ normalizer (K : Set G) := hRP.trans hPK
  have hSR : (S : Subgroup K).map K.subtype ≤ R := by
    rw [hSm]
    exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
      (inf_le_left.trans hTP) hPTS
  have hc : center (K ⧸ pCore 2 K) = ⊥ := by
    apply bot_unique
    intro z hz
    apply eK.injective
    have he := (MulEquivClass.apply_mem_center_iff eK).mpr hz
    change eK z ∈ center (alternatingGroup (Fin 5)) at he
    rw [alternatingGroup.center_eq_bot (by simp)] at he
    exact he.trans eK.map_one.symm
  let a : P →* MulAut (K ⧸ pCore 2 K) :=
    (pCoreJoinAction 2 hPK).comp (inclusion le_sup_right)
  let b := (MulAut.congr eK).toMonoidHom.comp a
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  let S' := S.mapSurjective hq
  have hact (x : P) (k : K) : b x (q k) =
      q (K.normalizerMonoidHom ⟨x,hPK x.property⟩ k) := by
    change eK (a x (eK.symm (eK (QuotientGroup.mk' (pCore 2 K) k)))) = _
    rw [eK.symm_apply_apply]
    exact congrArg eK (pCoreJoinAction_mk 2 hPK (inclusion le_sup_right x) k)
  have hS' (x : P) : (S' : Subgroup (alternatingGroup (Fin 5))).map (b x).toMonoidHom = S' := by
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (b x).injective])
    rintro z ⟨w,hw,rfl⟩
    obtain ⟨k,hk,rfl⟩ := hw
    change b x (q k) ∈ (S' : Subgroup (alternatingGroup (Fin 5)))
    rw [hact]
    apply mem_map_of_mem
    rw [hS] at hk ⊢
    exact ((mem_normalizer_iff.mp (hPTS x.property) k).mp ⟨hk,k.property⟩).1
  let BP := B.subgroupOf P
  have hBP3 : Nat.card BP = 3 := (Nat.card_congr (subgroupOfEquivOfLe hBP).toEquiv).trans hB3
  have hBperfect : IsPPerfect 2 BP := by
    intro N hn ht
    let := hn
    apply index_eq_one.mp
    change Nat.card (BP ⧸ N) = 1
    apply ht.card_eq_or_dvd.resolve_right
    intro hd
    have hd' := hd.trans N.card_quotient_dvd_card
    rw [hBP3] at hd'
    omega
  have hnon : ∃ d : BP, b d ≠ 1 := by
    by_contra hn
    push Not at hn
    have hBc : B ≤ K.pCoreIn 2 := by
      intro k hk
      let kK : K := ⟨k,hBK hk⟩
      let kP : P := ⟨k,hBP hk⟩
      have ha : a kP = 1 := (MulAut.congr eK).injective ((hn ⟨kP,hk⟩).trans (map_one _).symm)
      have hak : pCoreJoinAction 2 hPK (inclusion le_sup_left kK) = 1 := ha
      have hkcore : kK ∈ pCore 2 K := (pCoreJoinAction_restrict_ker 2 hPK hc).le hak
      exact mem_map_of_mem K.subtype hkcore
    have hh := ((isPGroup_pCoreIn 2 K).to_le hBc).card_eq_or_dvd
    rw [hB3] at hh
    omega
  have hinner : ∀ r : R, pCoreJoinAction 2 hRK (inclusion le_sup_right r) ∈
      MulAut.innerSubgroup (K ⧸ pCore 2 K) := by
    intro r
    obtain ⟨rr,hrr,he⟩ := r.property
    have hh := Theory.SpecificGroups.Alternating.FiveSylowRadical.normal_two_action_inner
      S' b hS' BP (pCore 2 P) hBperfect pCore_isPGroup hnon ⟨rr,hrr⟩
    rw [←MulAut.map_innerSubgroup_congr eK] at hh
    obtain ⟨u,hu,heu⟩ := hh
    have hae : a rr = u := (MulAut.congr eK).injective heu.symm
    have he' : pCoreJoinAction 2 hRK (inclusion le_sup_right r) = a rr := by
      ext z
      induction z using Quotient.inductionOn with | h k =>
        rw [show (⟦k⟧ : K ⧸ pCore 2 K) = QuotientGroup.mk' (pCore 2 K) k from rfl,
          pCoreJoinAction_mk 2]
        change _ = pCoreJoinAction 2 hPK (inclusion le_sup_right rr) _
        rw [pCoreJoinAction_mk 2]
        apply congrArg (QuotientGroup.mk' (pCore 2 K))
        apply Subtype.ext
        change (r : G) * (k : G) * (r : G)⁻¹ = (rr : G) * (k : G) * (rr : G)⁻¹
        change (rr : G) = (r : G) at he
        rw [he]
    rw [he',hae]
    exact hu
  have hf := sup_core_factor_of_inner_action K R hRK (isPGroup_pCoreIn 2 P) hc S hSR hinner
  have hRPnorm : P ≤ normalizer (R : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hXnorm : K ⊔ P ≤ normalizer ((K ⊔ R : Subgroup G) : Set G) :=
    sup_le ((show K ≤ K ⊔ R from le_sup_left).trans (K ⊔ R).le_normalizer)
      ((le_inf hPK hRPnorm).trans (K.normalizer_inf_normalizer_le_normalizer_sup R))
  have hecore : (K ⊔ R).pCoreIn 2 = (K ⊔ P).pCoreIn 2 := by
    apply le_antisymm (pCoreIn_mono_of_normalizes (sup_le_sup_left hRP K) hXnorm)
    have hXT : (K ⊔ P).pCoreIn 2 ≤ (T : Subgroup G) := by
      have hh := pCoreIn_le_sylow (K ⊔ P) (T.subtype (hTP.trans le_sup_right))
      change (K ⊔ P).pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf (K ⊔ P)).map (K ⊔ P).subtype at hh
      rwa [map_subgroupOf_eq_of_le (hTP.trans le_sup_right)] at hh
    have hXP : (K ⊔ P).pCoreIn 2 ≤ R :=
      (le_inf (hXT.trans hTP) le_rfl).trans (inf_pCoreIn_le_of_le 2 le_sup_right)
    exact (le_inf (hXP.trans le_sup_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 (sup_le_sup_left hRP K))
  simpa only [hSm,hecore] using hf

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.CartanCore

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original Cartan's two-core, on the literal old residual. -/
theorem source_old_residual_cartan_twoCore
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : (((pResidual 2 H).map H.subtype) ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hB3 : Nat.card B = 3)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G)) :
    (A ⊔ (T : Subgroup G)).pCoreIn 2 =
      ((T : Subgroup G) ⊓ (pResidual 2 H).map H.subtype) ⊔ (H ⊔ A).pCoreIn 2 := by
  let K := (pResidual 2 H).map H.subtype
  let P := A ⊔ (T : Subgroup G)
  have hHK : H ≤ normalizer (K : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))
  have hPK : P ≤ normalizer (K : Set G) := sup_le hAK (hH.1.1.2.trans hHK)
  have hAM : A ≤ D.maximalLocal :=
    hAB.trans ((map_subtype_le _).trans (inf_le_left.trans (localOrbit T L).le_normalizer))
  have hPM : P ≤ D.maximalLocal := sup_le hAM (le_normalizer_componentOrbit L T)
  have hK : ¬ K ≤ P := fun hk =>
    source_hstar_residual_not_le (le_normalizer_componentOrbit L T) hH (hk.trans hPM)
  have hf := CartanCore.core_factor T K P B hPK le_sup_right hK
    (hBA.trans le_sup_left) hBK hB3 eK
  have hj : K ⊔ P = H ⊔ A := by
    rw [←source_hstar_residual_sup_sylow hH]
    dsimp [K,P]
    ac_rfl
  simpa only [hj] using hf
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
