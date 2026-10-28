module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryComponentAction
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.OddPrime

/-!
# The odd-prime rows of the secondary component census

The actual alternating-four residual acts faithfully on the component, and
its normalizer in the selected Sylow image has index at most two. The cubic
rank-one action calculation therefore leaves exactly the parameters 5, 7
and 17. The canonical conjugation map and its Sylow image are retained.

Source: Aschbacher--Smith 2.4.29, printed pp.545--546.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.SmallBlocks.AlternatingSecondaryCensus
open ChapterC
private theorem cubic_block_of_equiv
    {A : Type*} [Group A] [Finite A] (hp : IsPPerfect 2 A)
    (e : A ≃* alternatingGroup (Fin 4)) :
    IsAlternatingBlock A 3 ∧ pCore 2 A = blockU A := by
  let eC : pCore 2 A ≃* pCore 2 (alternatingGroup (Fin 4)) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  have hc : Nat.card (pCore 2 A) = 4 := by
    rw [Nat.card_congr eC.toEquiv,AlternatingFourPair.twoCore_eq_kleinFour]
    exact alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)
  have he4 : IsElementaryAbelian 2 (pCore 2 (alternatingGroup (Fin 4))) := by
    rw [AlternatingFourPair.twoCore_eq_kleinFour]
    let hk := alternatingGroup.kleinFour_isKleinFour (by norm_num : Nat.card (Fin 4)=4)
    exact { toIsMulCommutative := hk.isMulCommutative
            exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  let := he4
  have he : IsElementaryAbelian 2 (pCore 2 A) :=
    IsElementaryAbelian.of_injective eC.toMonoidHom eC.injective
  have hq : Nat.card (A ⧸ pCore 2 A) = 3 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (pCore 2 A)
    rw [hc,Nat.card_congr e.toEquiv,alternatingGroup.card_of_card_eq_four (by norm_num)] at hh
    omega
  have hb := ChapterC.RankOne.Solvable.MinimalParabolic.alternatingThree_of_elementary_four_core
    hp he hc hq
  exact ⟨hb,hb.2.1.core_eq_blockU_of_quotient_three hq⟩

private theorem prime_model_ge_five
    {K : Type*} [Group K] [Group.IsPerfect K] {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hm : ClassicalGroup.IsPSL K 2 p) : 5 ≤ p := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    rcases hp.2 with ⟨k,hk⟩ | ⟨k,hk⟩
    · have hh : 2 ≤ 2^(2^k) := Nat.le_pow (by positivity)
      omega
    · have hk0 : k ≠ 0 := by intro he; simp [he] at hk
      have hh := dvd_pow_self 2 hk0
      rw [←hk] at hh
      norm_num at hh
  have hp3 : p ≠ 3 := by
    rintro rfl
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three hF
      (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
  have ho := hp.1.odd_of_ne_two hp2
  have hmin := hp.1.two_le
  obtain ⟨k,hk⟩ := ho
  omega

variable {G : Type*} [Group G] [Finite G]

theorem secondary_prime_component_parameter
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (u : G) (hu : orderOf u=2)
    (P : Sylow 2 (centralizer ({u} : Set G))) (M : Subgroup G) (z : G)
    (h115 : Chapter1.Lemma115Hypotheses (centralizer ({u} : Set G)) P M z)
    (L R K : Subgroup (centralizer ({u} : Set G)))
    (hL : IsPPerfect 2 L) (hK : IsComponent (centralizer ({u} : Set G)) K)
    (eA : L ≃* alternatingGroup (Fin 4))
    (a : L) (ha : a ∈ pCore 2 L) (hz : z=(a:G)*u)
    (hRL : R ≤ normalizer (L : Set (centralizer ({u} : Set G))))
    (hri : R.relIndex (P : Subgroup (centralizer ({u} : Set G))) ≤ 2)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hm : ClassicalGroup.IsPSL K 2 p) :
    p=5 ∨ p=7 ∨ p=17 := by
  let H := centralizer ({u} : Set G)
  let N := normalizer (K : Set H)
  have hn := secondary_component_residual_normalizes hG u hu L K hL hK
  let j : L →* N := inclusion hn
  let f := K.normalizerMonoidHom.comp j
  have hj : j.range = L.subgroupOf N := by
    ext n
    constructor
    · rintro ⟨l,rfl⟩
      exact l.property
    · intro hn
      exact ⟨⟨(n:H),hn⟩,rfl⟩
  have hr : f.range = (L.subgroupOf N).map K.normalizerMonoidHom := by
    rw [←hj]
    exact (MonoidHom.map_range _ _).symm
  obtain ⟨Q,_,hindex⟩ := secondary_component_residual_action_normalizer_bound
    hG u hu P L R K hL hK hRL hri
  obtain ⟨P₀,hP₀⟩ := K.exists_sylow_inner_le_normalizer_image Q
  have hf := (secondary_component_faithful_residual_action hG u hu P M z h115
    L K hL hK eA a ha hz).1
  let : IsQuasisimple K := hK.2
  let : Fact p.Prime := ⟨hp.1⟩
  have hp5 := prime_model_ge_five hp hm
  obtain ⟨F,_,_,hF,⟨e₀⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let e := e₀.trans (GorensteinWalter.psl2RingEquiv eF)
  obtain ⟨k,hk⟩ : ∃ k,p-1=2^k ∨ p+1=2^k := by
    rcases hp.2 with ⟨r,hpr⟩ | ⟨r,hpr⟩
    · exact ⟨2^r,Or.inl (by omega)⟩
    · exact ⟨r,Or.inr hpr⟩
  exact DoubleA3.prime_parameter_of_faithful_cubic_action
    (cubic_block_of_equiv hL eA).1 hp5 hk e f hf
    ((Q : Subgroup N).map K.normalizerMonoidHom) P₀ hP₀ (hr.symm ▸ hindex)

end CFSG.Quasithin.Chapter2.SmallBlocks.AlternatingSecondaryCensus
