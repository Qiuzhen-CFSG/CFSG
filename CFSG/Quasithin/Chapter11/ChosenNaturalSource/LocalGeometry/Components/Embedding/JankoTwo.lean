module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.SmallFinite
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowOvergroups.Coverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.PCoreFromTwoNormalizers

/-!
# Field-four matching for Hall--Janko relative components

The actual J₂ order leaves only degrees two and three for a nonbinary
PSL₂ section. A proper overgroup of a full Sylow lies in one of the checked
locals, of orders 1920 and 1152, so cannot contain the degree-three section.
If the normalized section and the Sylow generate J₂, perfectness makes
that section the whole group; its two-core quotient then has incompatible
order. Thus the original field has order four.

The proof restricts the actual relative Sylow to K and transports the
smaller quotient through the restricted two-group kernel of K → K/O₂(K).
It applies to both original flag normalizers and arbitrary nontrivial
U ≤ V₁ with the source N_T(U) Sylow condition. It neither discards O₂(Lᵢ)
nor assumes the smaller image is quasisimple.

The preceding quotient markings belong to qt-d-1222-natural-flag-cartan;
qt-d-1222-natural-local-geometry retains their final discharge. The relative
components owner applies the resulting field matching in Refinement.JankoTwo.
Source: Aschbacher--Smith A.3.12 and 11.1.1, printed pp.47--48,761,
combined manuscript of 1 March 2004. The imported ATLAS carrier and checked
Sylow-overgroup certificates retain their source attribution and license.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
open Sporadic.LeechRelated.J2

private theorem proper_sylow_overgroup_not_seven (S : Sylow 2 Carrier)
    (R : Subgroup Carrier) (hSR : (S : Subgroup Carrier) ≤ R) (hR : R ≠ ⊤) :
    ¬ 7 ∣ Nat.card R := by
  have hi : ¬ 2 ∣ R.index := fun h => S.not_dvd_index (h.trans (index_dvd_of_le hSR))
  obtain ⟨g,hg⟩ := exists_conj_overgroup_of_index_primeTo ExceptionalParabolics.Seed.s R
    (IsPGroup.of_card (n := 7) ExceptionalParabolics.PairNormalizer.card_s) hi
  let e := MulAut.conj g
  let U := R.comap e.toMonoidHom
  have hU : U ≠ ⊤ := by
    intro ht
    apply hR
    have hm := congrArg (map e.toMonoidHom) ht
    simpa only [U,map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      map_top_of_surjective e.toMonoidHom e.surjective] using hm
  have hc : Nat.card U = Nat.card R := by
    exact Nat.card_congr ((e.subgroupMap U).trans
      (MulEquiv.subgroupCongr (map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective R))).toEquiv
  intro hd
  rw [← hc] at hd
  rcases SylowOvergroups.proper_overgroup_le U hg hU with h | h
  · have hh := hd.trans (card_dvd_of_le h)
    rw [ExceptionalParabolics.FirstParabolic.card_l₁] at hh
    norm_num at hh
  · have hh := hd.trans (card_dvd_of_le h)
    rw [ExceptionalParabolics.PairNormalizer.card_p₂] at hh
    norm_num at hh

private theorem jankoTwo_section_parameter [Group.IsPerfect Carrier]
    (S : Sylow 2 Carrier) (B : Subgroup Carrier)
    (hnorm : (S : Subgroup Carrier) ≤ normalizer (B : Set Carrier))
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) : n = 2 := by
  have hd := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
  rw [binary_card hm,ExceptionalParabolics.FirstParabolic.card_carrier] at hd
  have hp : 2^n ∣ 604800 := (dvd_mul_right _ _).trans hd
  have hb : n < 8 := by
    by_contra! h
    have hbig := (show 2^8 ∣ 2^n from pow_dvd_pow 2 h).trans hp
    norm_num at hbig
  have hn23 : n = 2 ∨ n = 3 := by
    interval_cases n <;> norm_num at hn ⊢ <;> norm_num at hd
  rcases hn23 with hn | rfl
  · exact hn
  exfalso
  have h7 : 7 ∣ Nat.card B := by
    have hc := card_quotient_dvd_card (pCore 2 B)
    rw [binary_card hm] at hc
    exact (by decide : 7 ∣ 2^3 * ((2^3)^2-1)).trans hc
  have hj : B ⊔ (S : Subgroup Carrier) = ⊤ := by
    by_contra hj
    exact proper_sylow_overgroup_not_seven S _ le_sup_right hj
      (h7.trans (card_dvd_of_le (show B ≤ B ⊔ (S : Subgroup Carrier) from le_sup_left)))
  let : B.Normal := normalizer_eq_top_iff.mp (top_unique (hj ▸ sup_le B.le_normalizer hnorm))
  let : Group.IsNilpotent (Carrier ⧸ B) :=
    (isPGroup_quotient_of_sup_eq_top B (S : Subgroup Carrier) S.isPGroup' hj).isNilpotent
  have he : B = ⊤ := top_unique (by simpa only [solvableResidual_eq_top] using
    solvableResidual_le_of_solvable_quotient B)
  have h5 : 5 ∣ Nat.card B := by
    rw [he,Nat.card_congr (topEquiv (G := Carrier)).toEquiv,
      ExceptionalParabolics.FirstParabolic.card_carrier]
    decide
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B),binary_card hm] at h5
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
  rw [hk] at h5
  rcases (by decide : Nat.Prime 5).dvd_mul.mp h5 with hh | hh
  · norm_num at hh
  · have hh := (by decide : Nat.Prime 5).dvd_of_dvd_pow hh
    norm_num at hh

variable {G : Type*} [Group G] [Finite G]

private theorem jankoTwo_model_parameter [Group.IsPerfect G]
    (S : Sylow 2 G) (B : Subgroup G)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (e : G ≃* Carrier) : n = 2 := by
  let : Group.IsPerfect Carrier := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  let b := e.subgroupMap B
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  apply jankoTwo_section_parameter (S.mapSurjective e.surjective) (B.map e.toMonoidHom)
    ((map_mono hSB).trans (B.le_normalizer_map e.toMonoidHom)) hn
    (hm.of_mulEquiv bq.symm)

private theorem local_jankoTwo_parameters
    (P : Sylow 2 G) {B K : Subgroup G} (hK : K.IsCComponent) (hBK : B ≤ K)
    (hPB : (P : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (e : (K ⧸ pCore 2 K) ≃* Carrier) : n = 2 := by
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
  exact jankoTwo_model_parameter (Q.mapSurjective (QuotientGroup.mk'_surjective _))
    (C.map q) ((map_mono hQC).trans (C.le_normalizer_map q)) hn
    (hm.of_mulEquiv (a.symm.trans dq)) e

/-- The full relative Sylow forces field four in the actual Hall--Janko
quotient, preserving the smaller subgroup's intrinsic two-core. -/
theorem relative_jankoTwo_parameters
    {H B K P : Subgroup G} (hP : Chapter1.IsSylowIn 2 P H)
    (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    (hPB : P ≤ normalizer (B : Set G)) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Carrier)) : n = 2 := by
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
  exact local_jankoTwo_parameters P₀ hK.2 (comap_mono hBK) hnB hn
    (hm.of_mulEquiv bq) (kq.trans hmodel.some)

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Field-four matching at either original flag normalizer. -/
theorem flag_jankoTwo_parameters (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Carrier)) :
    S.field.degree = 2 := by
  have hTV : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) :=
    f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hTV,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTV]⟩
  exact relative_jankoTwo_parameters hs hK hLK (f.sylow_normalizes_Li i)
    S.nonbinary hm hmodel

/-- The J₂ alternative in 11.1.1 for both original flag normalizers. -/
theorem flag_component_alternative_of_jankoTwo (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Carrier)) :
    ComponentAlternative (f.Li i) K S.field.degree :=
  .four (flag_jankoTwo_parameters D S f i hm hK hLK hmodel) (.j2 hmodel)

/-- The arbitrary-subspace clause retains its original N_T(U) Sylow condition. -/
theorem subspace_component_alternative_of_jankoTwo
    (U : Subgroup G) (_hU : U ≠ ⊥) (_hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Carrier)) :
    ComponentAlternative (f.Li 0) K S.field.degree :=
  .four (relative_jankoTwo_parameters hSyl hK hLK
    (inf_le_left.trans (f.sylow_normalizes_Li 0)) S.nonbinary hm hmodel) (.j2 hmodel)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
