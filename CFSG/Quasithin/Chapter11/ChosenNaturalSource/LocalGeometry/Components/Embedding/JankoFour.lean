module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.RankOne
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismOrder
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFourPlacement
public import Theory.SpecificGroups.Janko4.BinaryEightSection
public import CFSG.Quasithin.MainConverse.SporadicLocal.J4
public import Theory.GroupAction.SubgroupCentralizerCongruence

/-!
# Field-four matching for J₄ relative components

The actual J₄ order restricts the nonbinary PSL₂ two-core section to fields
four, eight and thirty-two. The certified exponent-three Sylow subgroups
exclude field eight. At field thirty-two a trivial smaller two-core would
make the full J₄ Sylow act faithfully on PSL₂(32), contradicting the
binary automorphism order. A nontrivial core supplies a common normal
elementary subgroup. The certified full-Sylow catalogue puts the pair in
the Mathieu local or gives a normal elementary subgroup of order at most
eight. The former has no factor 31; in the latter an element of order 31
would fix a nonidentity involution, contradicting the actual centralizer
orders. Thus only the original field four remains.

The relative restriction and the literal containing-component quotient
preserve the smaller subgroup's intrinsic two-core. Applications retain
both flag normalizers and arbitrary nontrivial U ≤ V₁ with the original
N_T(U) Sylow condition. Refinement.JankoFour uses this field comparison to
discharge the first-normalizer cubic exclusion; the second-normalizer
exclusion is already proved in Refinement.SecondLargeSporadic on full V₂.

The preceding quotient markings belong to qt-d-1222-natural-flag-cartan,
with discharge by qt-d-1222-natural-local-geometry. The relative-components
owner retains the exhaustive catalogue, remaining refinements and triangle.
Source: Aschbacher--Smith A.3.12 and 11.1.1--11.1.2, printed pp.47--48,
761--765, combined manuscript of 1 March 2004; GLS3 Table 5.3i.
The imported concrete carriers and checked local certificates retain their
source attribution and licenses. No new finite enumeration is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open CFSG.Quasithin.ChapterA.Section03 CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
namespace JankoFour
open Janko4 Janko4.Cardinality Janko4.LocalStructure Janko4.OuterReduction.OddIndex
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
local notation "M" => max1Subgroup matrixA_mul_self matrixB_pow_four

private theorem involution_not_thirtyOne (z : Model) (hz : orderOf z = 2) :
    ¬ 31 ∣ Nat.card (centralizer ({z} : Set Model)) := by
  rcases InvolutionCentralizers.centralizer_equiv_first_or_second z hz with h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, OuterReduction.OddIndex.modelCentralizer_card]
    norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, InvolutionCentralizers.Second.ambient_card]
    norm_num

private theorem small_normal_elementary_not_thirtyOne
    (H A : Subgroup Model) (h31 : 31 ∣ Nat.card H)
    (hA : A ≠ ⊥) (he : IsElementaryAbelian 2 A) (hcard : Nat.card A ≤ 8)
    (hHA : H ≤ normalizer (A : Set Model)) : False := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  let := he
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 31 h31
  have hxo : orderOf (x : Model) = 31 := (orderOf_coe x).trans hx
  let P := zpowers (x : Model)
  have hP : IsPGroup 31 P := IsPGroup.of_card (n := 1) (by
    simpa only [P,Nat.card_zpowers,pow_one] using hxo)
  have hfixed : A ⊓ centralizer (P : Set Model) = ⊥ := by
    apply bot_unique
    intro z hz
    apply mem_bot.mpr
    by_contra hzne
    have hzord : orderOf z = 2 := orderOf_eq_prime_iff.mpr
      ⟨elemPow_eq_one_of_isElementaryAbelian z hz.1,hzne⟩
    have hxC : (x : Model) ∈ centralizer ({z} : Set Model) :=
      mem_centralizer_singleton_iff.mpr (hz.2 (x : Model) (mem_zpowers (x : Model)))
    have hxc : orderOf (⟨(x : Model),hxC⟩ : centralizer ({z} : Set Model)) = 31 :=
      (orderOf_coe _).symm.trans hxo
    exact involution_not_thirtyOne z hzord
      (hxc ▸ orderOf_dvd_natCard (⟨(x : Model),hxC⟩ : centralizer ({z} : Set Model)))
  have hmod := card_modEq_card_inf_centralizer P A hP
    ((zpowers_le.mpr x.property).trans hHA)
  rw [hfixed,card_bot] at hmod
  exact hA (A.eq_bot_of_card_eq (hmod.eq_of_lt_of_lt (by omega) (by decide)))

private def markedSylow : Sylow 2 Model :=
  twoSubgroup_isPGroup.toSylow (by
    rw [twoSubgroup,index_map_subtype,localTwoSubgroup_index]
    exact Nat.Prime.not_dvd_mul Nat.prime_two (by decide)
      Janko4.OuterReduction.max1_odd_index_unconditional)

private theorem normal_elementary_not_thirtyOne
    (S : Sylow 2 Model) (H E : Subgroup Model)
    (hSH : (S : Subgroup Model) ≤ H) (h31 : 31 ∣ Nat.card H)
    (hES : E ≤ (S : Subgroup Model)) (hE : E ≠ ⊥)
    (he : IsElementaryAbelian 2 E) (hHE : H ≤ normalizer (E : Set Model)) : False := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model S markedSylow
  let a := MulAut.conj g
  have hS : (S : Subgroup Model).map a.toMonoidHom = twoSubgroup :=
    congrArg Sylow.toSubgroup hg
  have h31' : 31 ∣ Nat.card (H.map a.toMonoidHom) := by
    rwa [card_map_of_injective a.injective]
  have hSH' := map_mono (f := a.toMonoidHom) hSH
  have hES' := map_mono (f := a.toMonoidHom) hES
  rw [hS] at hSH' hES'
  let := he
  rcases FiveLocalFF.JankoFour.fixed_pair_minimal_alternative
    (H.map a.toMonoidHom) (E.map a.toMonoidHom) hES'
    (fun hz => hE ((map_eq_bot_iff_of_injective _ a.injective).mp hz))
    (IsElementaryAbelian.map _) hSH'
    ((map_mono hHE).trans (E.le_normalizer_map a.toMonoidHom)) with h | ⟨A,hA,_,hAe,hAc,hHA⟩
  · have hd := h31'.trans (card_dvd_of_le h)
    rw [max1Subgroup_card] at hd
    norm_num at hd
  · exact small_normal_elementary_not_thirtyOne _ A h31' hA hAe hAc hHA

private theorem core_not_thirtyOne (S : Sylow 2 Model) (B : Subgroup Model)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (hc : pCore 2 B ≠ ⊥) (h31 : 31 ∣ Nat.card B) : False := by
  obtain ⟨N,hN,hBN,hSN⟩ := FiveLocalFF.SolvableQuotients.exists_maximal_two_local S B hn hc
  obtain ⟨R,hR,_,heR,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le S hN hSN
  let E := R.map (S : Subgroup Model).subtype
  let := heR
  exact normal_elementary_not_thirtyOne S N E hSN (h31.trans (card_dvd_of_le hBN))
    (map_subtype_le R) (fun hz => hR ((map_eq_bot_iff_of_injective _ Subtype.val_injective).mp hz))
    (IsElementaryAbelian.map _) (hNR ▸ le_rfl)

end JankoFour

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

variable {G : Type*} [Group G] [Finite G]

private theorem binary_aut_dvd (B : Subgroup G) [Group.IsPerfect B]
    (P : Sylow 2 G) (hPB : (P : Subgroup G) ≤ normalizer (B : Set G))
    (hE : IsEvenCharacteristicAt P) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL B 2 (2^n)) :
    Nat.card P ∣ (2^n * ((2^n)^2-1)) * n := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa using hF)
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
    rw [hF]
    exact (show (4:ℕ) = 2^2 from rfl).le.trans (Nat.pow_le_pow_right (by decide) hn))
  let : IsSimpleGroup B := e.isSimpleGroup
  have hz : center B = ⊥ := by
    rcases (inferInstance : (center B).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp hz)).elim
  let : IsQuasisimple B :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  let J := B ⊔ (P : Subgroup G)
  let C := B.subgroupOf J
  let a : C ≃* B := subgroupOfEquivOfLe le_sup_left
  let : C.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le B.le_normalizer hPB)
  have hC : IsComponent J C := ⟨(inferInstance : C.Normal).isSubnormal,
    IsQuasisimple.of_mulEquiv a.symm⟩
  have hlocal : B ∈ localCComponents P := hC.isCComponent
  have hf := sylow_centralizer_eq_bot_of_evenCharacteristic P hE hlocal hPB
  let φ := B.normalizerMonoidHom.comp (inclusion hPB)
  have hi : Function.Injective φ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hf]
    refine ⟨x.property,?_⟩
    change inclusion hPB x ∈ B.normalizerMonoidHom.ker at hx
    rw [normalizerMonoidHom_ker] at hx
    exact hx
  have ha : Nat.card (MulAut B) ∣ (2^n * ((2^n)^2-1)) * n := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact Theory.PSL2.BinaryAutomorphismOrder.aut_card_dvd hF
  exact (card_dvd_of_injective φ hi).trans ha

private theorem jankoFour_section_parameters (P : Sylow 2 Janko4.Model)
    (B : Subgroup Janko4.Model) [Group.IsPerfect B]
    (hPB : (P : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model))
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) : n = 2 := by
  have hd := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
  rw [binary_card hm,Janko4.Cardinality.model_card] at hd
  have hp : 2^n ∣ 86775571046077562880 := (dvd_mul_right _ _).trans hd
  have hb : n < 22 := by
    by_contra! h
    have hh := (show 2^22 ∣ 2^n from pow_dvd_pow 2 h).trans hp
    norm_num at hh
  have hn235 : n = 2 ∨ n = 3 ∨ n = 5 := by
    interval_cases n <;> norm_num at hn ⊢ <;> norm_num at hd
  rcases hn235 with rfl | rfl | rfl
  · rfl
  · exfalso
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (f := 3) (by simpa using hF)
    let a := e.trans (BenderSuzuki.ZD.Linear.sl2QuotientEquiv F).symm
    exact Janko4.no_binary_eight_quotient B (by simpa using hF)
      (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B)))
      (a.surjective.comp (QuotientGroup.mk'_surjective _))
  · exfalso
    have hc : pCore 2 B ≠ ⊥ := by
      intro hz
      let a : (B ⧸ pCore 2 B) ≃* B :=
        (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
      have hfaith := binary_aut_dvd B P hPB
        (MainConverse.SporadicLocal.j4_evenCharacteristic P) (by decide : 1 < 5)
        (hm.of_mulEquiv a.symm)
      have hpow : 2097152 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (n := 21) (by
        rw [Janko4.Cardinality.model_card]; decide)
      have bad := hpow.trans hfaith
      norm_num at bad
    apply JankoFour.core_not_thirtyOne P B hPB hc
    have hd := card_quotient_dvd_card (pCore 2 B)
    rw [binary_card hm] at hd
    exact (by decide : 31 ∣ 2^5 * ((2^5)^2-1)).trans hd

private theorem jankoFour_model_parameters (P : Sylow 2 G) (B : Subgroup G)
    [Group.IsPerfect B] (hPB : (P : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (e : G ≃* Janko4.Model) : n = 2 := by
  let b := e.subgroupMap B
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let : Group.IsPerfect (B.map e.toMonoidHom) := Group.IsPerfect.ofSurjective
    (f := b.toMonoidHom) b.surjective
  exact jankoFour_section_parameters (P.mapSurjective e.surjective) (B.map e.toMonoidHom)
    ((map_mono hPB).trans (B.le_normalizer_map e.toMonoidHom)) hn
    (hm.of_mulEquiv bq.symm)

private theorem local_jankoFour_parameters
    (P : Sylow 2 G) {B K : Subgroup G} (hK : K.IsCComponent) (hBK : B ≤ K)
    (hPB : (P : Subgroup G) ≤ normalizer (B : Set G)) [Group.IsPerfect B]
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (e : (K ⧸ pCore 2 K) ≃* Janko4.Model) : n = 2 := by
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_subnormal K hK.subnormal
  let C := B.subgroupOf K
  let q := QuotientGroup.mk' (pCore 2 K)
  have hQC : (Q : Subgroup K) ≤ normalizer (C : Set K) := by
    rw [hQ,← subgroupOf_normalizer_eq hBK]
    exact comap_mono hPB
  have hk : IsPGroup 2 (q.subgroupMap C).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let d := subgroupOfEquivOfLe hBK
  let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  let a := (q.subgroupMap C).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective C) hk
  let : Group.IsPerfect K := hK.perfect
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := d.symm.toMonoidHom) d.symm.surjective
  let : Group.IsPerfect (C.map q) := Group.IsPerfect.ofSurjective
    (f := q.subgroupMap C) (q.subgroupMap_surjective C)
  exact jankoFour_model_parameters (Q.mapSurjective (QuotientGroup.mk'_surjective _))
    (C.map q) ((map_mono hQC).trans (C.le_normalizer_map q)) hn
    (hm.of_mulEquiv (a.symm.trans dq)) e

/-- The full relative Sylow forces field four in the actual J₄
quotient, preserving the smaller subgroup's intrinsic two-core. -/
theorem relative_jankoFour_parameters
    {H B K P : Subgroup G} [Group.IsPerfect B] (hP : Chapter1.IsSylowIn 2 P H)
    (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    (hPB : P ≤ normalizer (B : Set G)) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) : n = 2 := by
  obtain ⟨P₀,hP₀⟩ := hP
  have hBH : B ≤ H := hBK.trans hK.1
  have hnB : (P₀ : Subgroup H) ≤ normalizer (B.subgroupOf H : Set H) := by
    intro p hp b
    change (b : G) ∈ B ↔ (p : G) * (b : G) * (p : G)⁻¹ ∈ B
    exact hPB (hP₀ ▸ mem_map_of_mem H.subtype hp) b
  let b := subgroupOfEquivOfLe hBH
  let k := subgroupOfEquivOfLe hK.1
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let kq := QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  let : Group.IsPerfect (B.subgroupOf H) := Group.IsPerfect.ofSurjective
    (f := b.symm.toMonoidHom) b.symm.surjective
  exact local_jankoFour_parameters P₀ (B := B.subgroupOf H) (K := K.subgroupOf H) hK.2 (comap_mono hBK) hnB hn
    (hm.of_mulEquiv bq) (kq.trans hmodel.some)

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Field-four matching at either original flag normalizer. -/
theorem flag_jankoFour_parameters (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) :
    S.field.degree = 2 := by
  have hTV : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) :=
    f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hTV,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTV]⟩
  let : Group.IsPerfect (f.Li i) := localResidual_perfect _
  exact relative_jankoFour_parameters hs hK hLK (f.sylow_normalizes_Li i)
    S.nonbinary hm hmodel

/-- The J₄ alternative in 11.1.1 for both original flag normalizers. -/
theorem flag_component_alternative_of_jankoFour (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) :
    ComponentAlternative (f.Li i) K S.field.degree :=
  .four (flag_jankoFour_parameters D S f i hm hK hLK hmodel) (.j4 hmodel)

/-- The arbitrary-subspace clause retains its original N_T(U) Sylow condition. -/
theorem subspace_component_alternative_of_jankoFour
    (U : Subgroup G) (_hU : U ≠ ⊥) (_hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) :
    ComponentAlternative (f.Li 0) K S.field.degree := by
  let : Group.IsPerfect (f.Li 0) := localResidual_perfect _
  exact .four (relative_jankoFour_parameters hSyl hK hLK
    (inf_le_left.trans (f.sylow_normalizes_Li 0)) S.nonbinary hm hmodel) (.j4 hmodel)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
