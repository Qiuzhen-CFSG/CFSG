module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.RankOne
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismOrder
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.TwoLocalOrder

/-!
# Field-four matching for Rudvalis relative components

The actual Rudvalis order restricts a nonbinary PSL₂ two-core section to
field degrees two, three or six. In the latter two degrees, a trivial
smaller two-core makes the full normalizing Sylow act faithfully on PSL₂.
Its automorphism order cannot contain the Rudvalis Sylow order. A
nontrivial smaller two-core instead puts both the section and the full
Sylow in its two-local normalizer. The checked Rudvalis local catalogue
excludes a factor nine there, whereas both remaining PSL₂ sections have it.
Thus the original field has order four.

Restriction to the relative containing component and passage through its
literal two-core preserve the smaller two-core quotient and its perfectness.
Both original flag normalizers and arbitrary nontrivial U ≤ V₁ retain
their source Sylow hypotheses. Refinement.Rudvalis applies this comparison
to the first-normalizer cubic exclusion; the second-normalizer exclusion
is already proved in Refinement.SecondLargeSporadic on all of V₂.

The preceding quotient markings belong to qt-d-1222-natural-flag-cartan,
with discharge by qt-d-1222-natural-local-geometry. The relative-components
owner retains the exhaustive catalogue, other refinements and triangle.
Source: Aschbacher--Smith A.3.12 and 11.1.1--11.1.2, printed pp.47--48,
761--765, combined manuscript of 1 March 2004; GLS3 Table 5.3r, p.279.
The imported concrete carriers and checked local certificates retain their
source attribution and licenses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open CFSG.Quasithin.ChapterA.Section03 CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
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

private theorem rudvalis_section_parameters (P : Sylow 2 G) (B : Subgroup G)
    [Group.IsPerfect B] (hPB : (P : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (e : G ≃* Rudvalis.Model) : n = 2 := by
  have hc : Nat.card G = 145926144000 := (Nat.card_congr e.toEquiv).trans Rudvalis.model_card
  have hd := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
  rw [binary_card hm,hc] at hd
  have hp : 2^n ∣ 145926144000 := (dvd_mul_right _ _).trans hd
  have hb : n < 15 := by
    by_contra! h
    have hh := (show 2^15 ∣ 2^n from pow_dvd_pow 2 h).trans hp
    norm_num at hh
  have hn236 : n = 2 ∨ n = 3 ∨ n = 6 := by
    interval_cases n <;> norm_num at hn ⊢ <;> norm_num at hd
  rcases hn236 with hh | hh
  · exact hh
  exfalso
  have hcore : pCore 2 B ≠ ⊥ := by
    intro hz
    let a : (B ⧸ pCore 2 B) ≃* B :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    have hfaith := binary_aut_dvd B P hPB
      (MainConverse.evenCharacteristic_of_model_equiv e
        MainConverse.SporadicLocal.ru_evenCharacteristic P) hn (hm.of_mulEquiv a.symm)
    have hpow : 16384 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (n := 14) (by
      rw [hc]; decide)
    have bad := hpow.trans hfaith
    rcases hh with rfl | rfl <;> norm_num at bad
  let U := (pCore 2 B).map B.subtype
  have hU : U ≠ ⊥ := fun hz => hcore ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp hz)
  let N := normalizer (U : Set G)
  have hBN : B ≤ N := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hPN : (P : Subgroup G) ≤ N := hPB.trans
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hlocal : IsTwoLocal N := ⟨U,hU,pCore_isPGroup.map B.subtype,rfl⟩
  have hnine := Rudvalis.SylowOvergroups.not_nine_dvd_card_twoLocal
    (P.mapSurjective e.surjective) (N.map e.toMonoidHom)
    (Theory.Quasithin.isTwoLocal_map e hlocal) (map_mono hPN)
  rw [card_map_of_injective e.injective] at hnine
  apply hnine
  apply dvd_trans _ (card_dvd_of_le hBN)
  apply dvd_trans _ (card_quotient_dvd_card (pCore 2 B))
  rw [binary_card hm]
  rcases hh with rfl | rfl <;> decide


private theorem local_rudvalis_parameters
    (P : Sylow 2 G) {B K : Subgroup G} (hK : K.IsCComponent) (hBK : B ≤ K)
    (hPB : (P : Subgroup G) ≤ normalizer (B : Set G)) [Group.IsPerfect B]
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (e : (K ⧸ pCore 2 K) ≃* Rudvalis.Model) : n = 2 := by
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
  exact rudvalis_section_parameters (Q.mapSurjective (QuotientGroup.mk'_surjective _))
    (C.map q) ((map_mono hQC).trans (C.le_normalizer_map q)) hn
    (hm.of_mulEquiv (a.symm.trans dq)) e

/-- The full relative Sylow forces field four in the actual Rudvalis
quotient, preserving the smaller subgroup's intrinsic two-core. -/
theorem relative_rudvalis_parameters
    {H B K P : Subgroup G} [Group.IsPerfect B] (hP : Chapter1.IsSylowIn 2 P H)
    (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    (hPB : P ≤ normalizer (B : Set G)) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Rudvalis.Model)) : n = 2 := by
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
  exact local_rudvalis_parameters P₀ (B := B.subgroupOf H) (K := K.subgroupOf H) hK.2 (comap_mono hBK) hnB hn
    (hm.of_mulEquiv bq) (kq.trans hmodel.some)

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Field-four matching at either original flag normalizer. -/
theorem flag_rudvalis_parameters (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Rudvalis.Model)) :
    S.field.degree = 2 := by
  have hTV : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) :=
    f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hTV,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTV]⟩
  let : Group.IsPerfect (f.Li i) := localResidual_perfect _
  exact relative_rudvalis_parameters hs hK hLK (f.sylow_normalizes_Li i)
    S.nonbinary hm hmodel

/-- The Rudvalis alternative in 11.1.1 for both original flag normalizers. -/
theorem flag_component_alternative_of_rudvalis (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Rudvalis.Model)) :
    ComponentAlternative (f.Li i) K S.field.degree :=
  .four (flag_rudvalis_parameters D S f i hm hK hLK hmodel) (.ru hmodel)

/-- The arbitrary-subspace clause retains its original N_T(U) Sylow condition. -/
theorem subspace_component_alternative_of_rudvalis
    (U : Subgroup G) (_hU : U ≠ ⊥) (_hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Rudvalis.Model)) :
    ComponentAlternative (f.Li 0) K S.field.degree := by
  let : Group.IsPerfect (f.Li 0) := localResidual_perfect _
  exact .four (relative_rudvalis_parameters hSyl hK hLK
    (inf_le_left.trans (f.sylow_normalizes_Li 0)) S.nonbinary hm hmodel) (.ru hmodel)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
