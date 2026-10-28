module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryComponentAbsorption
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.AlternatingActions
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115.Transport
public import BenderSuzuki.SE.ModelSylowInvolutions
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.BenderTwoKernel

/-!
# The marked residual actor and the Bender exclusion

The two-perfect residual cannot induce the odd alternating-six or
alternating-seven actions in 1.1.5. Its marked involution thus acts internally
on the selected component. For a Bender component, the projected four-group
absorption gives component normality. Square-one elements in a Bender Sylow
two-subgroup commute, contradicting the original two noncommuting four-groups.

Source: Aschbacher--Smith 2.4.29, printed pp.545--546.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
namespace CFSG.Quasithin.Chapter2.SmallBlocks.AlternatingSecondaryCensus

theorem inner_of_modelAction115_of_twoPerfect_actor
    {L K : Type*} [Group L] [Group K] [Group.IsPerfect K]
    (hL : IsPPerfect 2 L) (f : L →* MulAut K) (a : L)
    (hm : ModelAction115 K (f a)) : f a ∈ MulAut.innerSubgroup K := by
  cases hm with
  | lie _ _ hi => exact hi
  | two_cover _ _ _ hi => exact hi
  | odd _ hi => exact hi
  | sporadic _ _ _ hi => exact hi.1
  | six σ hs hact =>
    exact (DoubleA3.alternating_action_excluded_by_twoPerfect_actor
      hL f a 6 (.inl rfl) σ hs.sign_eq hact).elim
  | seven σ hs hact =>
    apply (DoubleA3.alternating_action_excluded_by_twoPerfect_actor
      hL f a 7 (.inr rfl) σ ?_ hact).elim
    rw [Equiv.Perm.sign_of_cycleType,hs]
    norm_num

variable {G : Type*} [Group G] [Finite G]

theorem secondary_component_marked_action_inner
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (u : G) (hu : orderOf u=2)
    (P : Sylow 2 (centralizer ({u}:Set G))) (M : Subgroup G) (z : G)
    (K : Subgroup (centralizer ({u}:Set G)))
    (c : ComponentRefinement.MathieuSourceSetup (centralizer ({u}:Set G))
      (K.map (centralizer ({u}:Set G)).subtype) M P z)
    (L : Subgroup (centralizer ({u}:Set G))) (hL : IsPPerfect 2 L)
    (hK : IsComponent (centralizer ({u}:Set G)) K)
    (_eA : L ≃* alternatingGroup (Fin 4))
    (a : L) (_ha : a ∈ pCore 2 L) (hz : z=(a:G)*u) :
    (K.normalizerMonoidHom.comp (inclusion
      (secondary_component_residual_normalizes hG u hu L K hL hK))) a
      ∈ MulAut.innerSubgroup K := by
  let H := centralizer ({u}:Set G)
  let A := K.map H.subtype
  let e : K ≃* A := K.equivMapOfInjective H.subtype H.subtype_injective
  let : IsQuasisimple K := hK.2
  obtain ⟨α,hα,hm⟩ := c.modelAction115 hG
    (fun X _ _ => ChapterA.Section02.theoremsABC_knownSimple (G := X))
  let β := MulAut.congr e.symm α
  have hmβ : ModelAction115 K β := hm.of_mulEquiv e
  let f := K.normalizerMonoidHom.comp (inclusion
    (secondary_component_residual_normalizes hG u hu L K hL hK))
  have heq : f a=β := by
    apply MulEquiv.ext
    intro k
    apply e.injective
    apply Subtype.ext
    have hku : u*(k:G)*u⁻¹=(k:G) := by
      rw [←mem_centralizer_singleton_iff.mp (k:H).property,mul_inv_cancel_right]
    change (a:G)*(k:G)*(a:G)⁻¹=(e (e.symm (α (e k))):G)
    rw [e.apply_symm_apply]
    rw [hα,hz]
    calc
      (a:G)*(k:G)*(a:G)⁻¹=(a:G)*(u*(k:G)*u⁻¹)*(a:G)⁻¹ := by rw [hku]
      _=((a:G)*u)*(k:G)*((a:G)*u)⁻¹ := by group
  exact inner_of_modelAction115_of_twoPerfect_actor hL f a (heq.symm ▸ hmβ)

 theorem bender_row_false_of_normal_core_conjugates
    {H : Type*} [Group H] [Finite H] (P : Sylow 2 H) (K E : Subgroup H)
    [K.Normal] [IsElementaryAbelian 2 E]
    (hEK : E ≤ K) (hEP : E ≤ (P : Subgroup H))
    (x : H) (hx : x ∈ P)
    (hnc : ¬ E.map (MulAut.conj x).toMonoidHom ≤ centralizer (E : Set H))
    (hb : ClassificationModels.IsBenderModel K) : False := by
  have hB := Chapter1.QuasisimpleInvolutions.isSimpleBenderGroup_of_benderModel hb
  apply hnc
  rintro _ ⟨v,hv,rfl⟩ e he
  have hvK : x*v*x⁻¹ ∈ K := (mem_normalizer_iff.mp
    (show x ∈ normalizer (K : Set H) by rw [normalizer_eq_top]; trivial) v).mp (hEK hv)
  have hvP : x*v*x⁻¹ ∈ P := P.toSubgroup.mul_mem
    (P.toSubgroup.mul_mem hx (hEP hv)) (P.toSubgroup.inv_mem hx)
  let s : K := ⟨x*v*x⁻¹,hvK⟩
  let t : K := ⟨e,hEK he⟩
  have hs : s^2=1 := by
    apply Subtype.ext
    change ((MulAut.conj x) v)^2=1
    rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv,map_one]
  have ht : t^2=1 := by
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) e he
  exact congrArg Subtype.val (hB.squares_commute_in_twoSubgroup
    ((P : Subgroup H).subgroupOf K) P.isPGroup'.comap_subtype s t hvP (hEP he) hs ht).eq.symm


theorem secondary_bender_component_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (u : G) (hu : orderOf u=2)
    (P : Sylow 2 (centralizer ({u}:Set G))) (M : Subgroup G) (z : G)
    (K : Subgroup (centralizer ({u}:Set G)))
    (c : ComponentRefinement.MathieuSourceSetup (centralizer ({u}:Set G))
      (K.map (centralizer ({u}:Set G)).subtype) M P z)
    (h115 : Chapter1.Lemma115Hypotheses (centralizer ({u}:Set G)) P M z)
    (L R : Subgroup (centralizer ({u}:Set G))) (hL : IsPPerfect 2 L)
    (hK : IsComponent (centralizer ({u}:Set G)) K)
    (eA : L ≃* alternatingGroup (Fin 4))
    (a : L) (ha : a ∈ pCore 2 L) (hz : z=(a:G)*u)
    (hEP : (pCore 2 L).map L.subtype ≤ (P : Subgroup (centralizer ({u}:Set G))))
    (hRL : R ≤ normalizer (L : Set (centralizer ({u}:Set G))))
    (hri : R.relIndex (P : Subgroup (centralizer ({u}:Set G))) ≤ 2)
    (ho : pPrimeCore 2 (centralizer ({u}:Set G))=⊥)
    (x : centralizer ({u}:Set G)) (hx : x ∈ P)
    (hnc : ¬ ((pCore 2 L).map L.subtype).map (MulAut.conj x).toMonoidHom ≤
      centralizer (((pCore 2 L).map L.subtype : Subgroup (centralizer ({u}:Set G))) : Set (centralizer ({u}:Set G))))
    (hb : ClassificationModels.IsBenderModel K) : False := by
  have hB := Chapter1.QuasisimpleInvolutions.isSimpleBenderGroup_of_benderModel hb
  let : IsSimpleGroup K := hB.isSimple
  have hzK : center K=⊥ := by
    apply (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) inferInstance).resolve_right
    intro hh
    apply hB.not_commutative
    intro k l
    exact (mem_center_iff.mp (hh.symm ▸ mem_top k) l).symm
  have hinner := secondary_component_marked_action_inner hG u hu P M z K c L hL hK eA a ha hz
  have hEK := secondary_component_core_le_of_inner hG u hu P M z h115 L R K hL hK eA a ha hz
    hzK hinner hEP hRL hri
  have hstructure := secondary_component_structure_of_inner hG u hu P M z h115 L R K hL hK eA a ha hz
    hzK hinner hEP hRL hri ho
  let : K.Normal := hstructure.1
  let E := (pCore 2 L).map L.subtype
  have hc := pCore_map_iso 2 eA
  have he4 : IsElementaryAbelian 2 (pCore 2 (alternatingGroup (Fin 4))) := by
    rw [AlternatingFourPair.twoCore_eq_kleinFour]
    let hk := alternatingGroup.kleinFour_isKleinFour (by norm_num : Nat.card (Fin 4)=4)
    exact { toIsMulCommutative := hk.isMulCommutative
            exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  let eC : pCore 2 L ≃* pCore 2 (alternatingGroup (Fin 4)) :=
    (eA.subgroupMap _).trans (MulEquiv.subgroupCongr hc)
  let := he4
  let : IsElementaryAbelian 2 (pCore 2 L) := IsElementaryAbelian.of_injective eC.toMonoidHom eC.injective
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map L.subtype
  exact bender_row_false_of_normal_core_conjugates P K E hEK hEP x hx hnc hb

end CFSG.Quasithin.Chapter2.SmallBlocks.AlternatingSecondaryCensus
