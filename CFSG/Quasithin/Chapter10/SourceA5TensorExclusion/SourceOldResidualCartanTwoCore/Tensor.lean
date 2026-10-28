module
public import Theory.SpecificGroups.Alternating.FivePairSylowRadical
public import Theory.GroupTheory.PCoreQuotientInnerSupplement
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaChief
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanTwoCore.Residual

/-!
# The tensor side of the original Cartan two-core equality

Let P = AT and Q = O₂(L₀T). The actual Borel placement makes T ∩ L₀
normal in P. On the original A₅-pair quotient, the marked order-nine torus
forces O₂(P) to act by inner automorphisms. The inner-action supplement
formula therefore gives O₂(P) = (T ∩ L₀)O₂(L₀O₂(P)). Normality and the
original Sylow subgroup identify the latter core with Q.

The final theorem combines this equality with the old-residual calculation
on the same G, T, L, H and A. Its remaining premises are the earlier source
A₅ recognition, cubic Cartan and Cartan normalization statements.
Source: Aschbacher--Smith, Lemma 9.3.2, printed p.733.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- The original order-nine Borel torus has precisely the tensor two-core. -/
theorem source_tensor_cartan_twoCore
    (A : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9) :
    (A ⊔ (T : Subgroup G)).pCoreIn 2 =
      ((T : Subgroup G) ⊓ localOrbit T L) ⊔ (localJoin T L).pCoreIn 2 := by
  let K := localOrbit T L
  let P := A ⊔ (T : Subgroup G)
  have hAK : A ≤ K := hAB.trans ((map_subtype_le _).trans inf_le_left)
  have hAN : A ≤ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    hAB.trans ((map_subtype_le _).trans inf_le_right)
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) := le_normalizer_componentOrbit L T
  have hPK : P ≤ normalizer (K : Set G) := sup_le (hAK.trans K.le_normalizer) hTK
  have hTP : (T : Subgroup G) ≤ P := le_sup_right
  have hPTS : P ≤ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    sup_le hAN ((le_inf (T : Subgroup G).le_normalizer hTK).trans inf_normalizer_le_normalizer_inf)
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  have hSm : (S : Subgroup K).map K.subtype = (T : Subgroup G) ⊓ K := by
    rw [hS,subgroupOf_map_subtype]
  let R := P.pCoreIn 2
  have hRP : R ≤ P := P.pCoreIn_le 2
  have hRK : R ≤ normalizer (K : Set G) := hRP.trans hPK
  have hSR : (S : Subgroup K).map K.subtype ≤ R := by
    rw [hSm]
    exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
      (inf_le_left.trans hTP) hPTS
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp m.sylow_not_normalizes_component
  obtain ⟨q0,hq0,hk0,_⟩ := source_a5_original_product_quotient D e
    m.sylow_not_normalizes_component ht htn
  let eqK : (K ⧸ pCore 2 K) ≃* (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :=
    (QuotientGroup.quotientMulEquivOfEq hk0.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q0 hq0)
  have hc : center (K ⧸ pCore 2 K) = ⊥ := by
    apply bot_unique
    intro z hz
    apply eqK.injective
    have he := (MulEquivClass.apply_mem_center_iff eqK).mpr hz
    change eqK z ∈ center (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) at he
    rw [Subgroup.center_prod,alternatingGroup.center_eq_bot (by simp),bot_prod_bot] at he
    exact he.trans eqK.map_one.symm
  let a : P →* MulAut (K ⧸ pCore 2 K) :=
    (pCoreJoinAction 2 hPK).comp (inclusion le_sup_right)
  let b := (MulAut.congr eqK).toMonoidHom.comp a
  let q := eqK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eqK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    ext x
    change eqK (QuotientGroup.mk' (pCore 2 K) x) = 1 ↔ x ∈ pCore 2 K
    rw [map_eq_one_iff eqK eqK.injective]
    exact QuotientGroup.eq_one_iff x
  let S' := S.mapSurjective hq
  have hact (x : P) (k : K) : b x (q k) =
      q (K.normalizerMonoidHom ⟨x,hPK x.property⟩ k) := by
    change eqK (a x (eqK.symm (eqK (QuotientGroup.mk' (pCore 2 K) k)))) = _
    rw [eqK.symm_apply_apply]
    exact congrArg eqK (pCoreJoinAction_mk 2 hPK (inclusion le_sup_right x) k)
  have hS' (x : P) : (S' : Subgroup _).map (b x).toMonoidHom = S' := by
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (b x).injective])
    rintro z ⟨w,hw,rfl⟩
    obtain ⟨k,hk,rfl⟩ := hw
    change b x (q k) ∈ (S' : Subgroup _)
    rw [hact]
    apply mem_map_of_mem
    rw [hS] at hk ⊢
    exact ((mem_normalizer_iff.mp (hPTS x.property) k).mp ⟨hk,k.property⟩).1
  let i : A →* P := inclusion le_sup_left
  let j : A →* K := inclusion hAK
  let qA := q.comp j
  have hA : IsPGroup 3 A := IsPGroup.of_card (n := 2) hA9
  have hqA : Function.Injective qA := by
    have hi := Theory.AlternatingFive.injective_on_three_subgroup q
      (hk ▸ (pCore_isPGroup (p := 2) (G := K))) (A.subgroupOf K) hA.comap_subtype
    exact hi.comp (subgroupOfEquivOfLe hAK).symm.injective
  have hi (d : A) : b (i d) = MulAut.conj (qA d) := by
    have he : a (i d) = MulAut.conj (QuotientGroup.mk' (pCore 2 K) (j d)) :=
      pCoreJoinAction_on_component 2 hPK (j d)
    change MulAut.congr eqK (a (i d)) = _
    rw [he]
    apply MulEquiv.ext
    intro z
    change eqK (QuotientGroup.mk' (pCore 2 K) (j d) * eqK.symm z *
      (QuotientGroup.mk' (pCore 2 K) (j d))⁻¹) =
      eqK (QuotientGroup.mk' (pCore 2 K) (j d)) * z *
        (eqK (QuotientGroup.mk' (pCore 2 K) (j d)))⁻¹
    simp only [map_mul,map_inv,eqK.apply_symm_apply]
  let AP := A.subgroupOf P
  let eqA : AP ≃* A := subgroupOfEquivOfLe (show A ≤ P from le_sup_left)
  let qAP := qA.comp eqA.toMonoidHom
  have hAP9 : Nat.card AP = 9 := (Nat.card_congr eqA.toEquiv).trans hA9
  have hAPact (d : AP) : b d = MulAut.conj (qAP d) := hi (eqA d)
  have hinner : ∀ r : R, pCoreJoinAction 2 hRK (inclusion le_sup_right r) ∈
      MulAut.innerSubgroup (K ⧸ pCore 2 K) := by
    intro r
    obtain ⟨rr,hrr,he⟩ := r.property
    have hh := Theory.SpecificGroups.Alternating.FivePairSylowRadical.normal_two_action_inner_of_marked_torus
      S' b hS' AP (pCore 2 P) hA.comap_subtype hAP9 pCore_isPGroup
      qAP (hqA.comp eqA.injective) hAPact ⟨rr,hrr⟩
    rw [←MulAut.map_innerSubgroup_congr eqK] at hh
    obtain ⟨u,hu,heu⟩ := hh
    have hae : a rr = u := (MulAut.congr eqK).injective heu.symm
    have he' : pCoreJoinAction 2 hRK (inclusion le_sup_right r) = a rr := by
      ext z
      induction z using Quotient.inductionOn with | h k =>
        rw [show (⟦k⟧ : K ⧸ pCore 2 K) = QuotientGroup.mk' (pCore 2 K) k from rfl,
          pCoreJoinAction_mk 2]
        change _ = pCoreJoinAction 2 hPK (inclusion le_sup_right rr) _
        rw [pCoreJoinAction_mk 2]
        apply congrArg (QuotientGroup.mk' (pCore 2 K))
        apply Subtype.ext
        change (r : G)*(k : G)*(r : G)⁻¹ = (rr : G)*(k : G)*(rr : G)⁻¹
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
  have hj : K ⊔ P = localJoin T L := by
    dsimp only [P]
    rw [←sup_assoc,sup_eq_left.mpr hAK]
  simpa only [hSm,hecore,hj] using hf


/-- The two descriptions of the source subgroup S agree on the original Cartan. -/
theorem source_cartan_twoCore_eq_old_residual
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : (((pResidual 2 H).map H.subtype) ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hB3 : Nat.card B = 3)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G)) :
    ((T : Subgroup G) ⊓ localOrbit T L) ⊔ (localJoin T L).pCoreIn 2 =
      ((T : Subgroup G) ⊓ (pResidual 2 H).map H.subtype) ⊔ (H ⊔ A).pCoreIn 2 :=
  (m.source_tensor_cartan_twoCore A hAB hA9).symm.trans
    (source_old_residual_cartan_twoCore D hH eK A B hAB hBA hBK hB3 hAK)
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
