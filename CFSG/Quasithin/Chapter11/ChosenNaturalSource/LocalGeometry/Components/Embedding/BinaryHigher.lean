module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.RankOne
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.BinaryLinear.Source
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.Classical.BinaryLinearThreeRank
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.GroupTheory.PrimeRankCoprimeIndex
public import Theory.Quasithin.CoprimeRank

/-!
# Excluding the higher binary linear relative-component carriers

The orders of PSL₄(2) and PSL₅(2) leave only field degrees two and
three for a nonbinary PSL₂ section. In degree three the section has
three-part nine, so its inverse image contains a full Sylow three-subgroup.
Its three-rank is at most one, contradicting the ambient elementary nine.
Degree two is excluded by the checked full-Sylow local A₅-section theorem.
The actual A₈ equivalence gives the remaining higher binary source row.

Restriction to the containing relative component and its intrinsic two-core
quotient retains the smaller subgroup's own two-core. No quasisimplicity
of the smaller image is assumed. The final containment applications cover
both original flag normalizers and every eligible nontrivial U ≤ V₁.
They remove these three rows from the exhaustive carrier assembly in
qt-d-1222-natural-relative-components. The earlier rank-one markings and
pointwise line action belong to qt-d-1222-natural-flag-cartan, with final
discharge in qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith A.3.12(4--5) and 11.1.1, printed pp.47--48,761,
combined manuscript of 1 March 2004. The imported carrier comparisons and
full-Sylow geometry retain their source attribution and licenses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin
open CFSG.Quasithin.ChapterA.Section03
open CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
variable {G : Type*} [Group G] [Finite G]

private theorem no_eight_section (B : Subgroup G)
    (h27 : ¬ 27 ∣ Nat.card G) (hr : 2 ≤ primeRank 3 G)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^3)) : False := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9B : 9 ∣ Nat.card B := by
    have hd := card_quotient_dvd_card (pCore 2 B)
    rw [binary_card hm] at hd
    exact (by decide : 9 ∣ 2^3 * ((2^3)^2-1)).trans hd
  have hi : ¬ 3 ∣ B.index := by
    intro h
    apply h27
    rw [←B.card_mul_index]
    exact Nat.mul_dvd_mul h9B h
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  let a := e.trans (BenderSuzuki.ZD.Linear.sl2QuotientEquiv F).symm
  have hle : primeRank 3 B ≤ 1 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup,
      primeRank_congr 3 a]
    exact Matrix.SL2.binary_odd_primeRank_le_one (by decide)
  rw [B.primeRank_eq_of_not_dvd_index hi] at hle
  omega

private theorem binary_projective_card (d : ℕ) [NeZero d] :
    Nat.card PSL(d,ZMod 2) = ∏ i : Fin d, (2^d-2^i.val) := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) d
  simpa only [Nat.card_zmod,show 2-1=1 from rfl,Nat.gcd_one_right,mul_one] using h

private theorem binary_higher_data {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hm : ClassicalGroup.IsPSL G d 2) :
    (Nat.card G = 20160 ∨ Nat.card G = 9999360) ∧ 2 ≤ primeRank 3 G := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let a := e.trans (Atlas.fieldEquivPSL d k)
  constructor
  · rw [Nat.card_congr a.toEquiv]
    rcases hd with rfl | rfl
    · left
      rw [binary_projective_card]
      decide
    · right
      rw [binary_projective_card]
      decide
  · let b := a.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < d))
    rw [primeRank_equiv 3 b]
    exact Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank (by omega)

private theorem binary_higher_section_parameter (B : Subgroup G) {n d : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hd : d = 4 ∨ d = 5) (hmodel : ClassicalGroup.IsPSL G d 2) : n = 2 := by
  obtain ⟨hc,hr⟩ := binary_higher_data hd hmodel
  have hv := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
  rw [binary_card hm] at hv
  have hp : 2^n ∣ Nat.card G := (dvd_mul_right _ _).trans hv
  have hb : n < 11 := by
    by_contra! h
    have hh := (show 2^11 ∣ 2^n from pow_dvd_pow 2 h).trans hp
    rcases hc with hc | hc <;> rw [hc] at hh <;> norm_num at hh
  have hn23 : n = 2 ∨ n = 3 := by
    interval_cases n <;> norm_num at hn ⊢ <;>
      rcases hc with hc | hc <;> norm_num [hc] at hv
  rcases hn23 with h | rfl
  · exact h
  · exact (no_eight_section B (by rcases hc with hc | hc <;> rw [hc] <;> decide) hr hm).elim

/-- A full-Sylow local component with a nonbinary PSL₂ two-core quotient
cannot lie in either higher binary linear carrier. -/
theorem not_local_binary_higher
    (P : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents P)
    {n d : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hd : d = 4 ∨ d = 5) (hmodel : ClassicalGroup.IsPSL G d 2) : False := by
  have hn2 := binary_higher_section_parameter B hn hm hd hmodel
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (show Nat.card F = 4 by simpa [hn2] using hF)
  exact SourceEmbeddings.FiveLocalFF.BinaryLinear.not_section_binary_linear P B hB
    (e.trans a) hd hmodel


/-- The three higher binary rows in the complete Theorem C catalogue.
The alternating row uses the actual eight-letter carrier. -/
@[expose] def HigherBinaryCarrier (A : Type*) [Group A] : Prop :=
  Chapter1.Section02.LocalModels.IsAlternating A 8 ∨
    ∃ d, (d = 4 ∨ d = 5) ∧ ClassicalGroup.IsPSL A d 2

private theorem higher_binary_model {A : Type*} [Group A]
    (h : HigherBinaryCarrier A) :
    ∃ d, (d = 4 ∨ d = 5) ∧ ClassicalGroup.IsPSL A d 2 := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    exact ⟨4,Or.inl rfl,ZMod 2,inferInstance,inferInstance,by simp,
      ⟨e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩⟩
  · exact h

private theorem local_not_higher_binary
    (P : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents P) (hK : K.IsCComponent) (hBK : B ≤ K)
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hmodel : HigherBinaryCarrier (K ⧸ pCore 2 K)) : False := by
  obtain ⟨d,hd,hmodel⟩ := higher_binary_model hmodel
  obtain ⟨R,_,hR⟩ := SourceEmbeddings.exists_local_sylow_restriction P hB hBK hK.subnormal
  let C := B.subgroupOf K
  let q := QuotientGroup.mk' (pCore 2 K)
  let : Group.IsNilpotent (pCore 2 K) := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  have hk : IsPGroup 2 (q.subgroupMap C).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let b := subgroupOfEquivOfLe hBK
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let a := (q.subgroupMap C).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective C) hk
  exact not_local_binary_higher (R.mapSurjective (QuotientGroup.mk'_surjective _))
    (C.map q) (Chapter1.Section02.localCComponents_map_of_solvable_ker hR q) hn
    (hm.of_mulEquiv (a.symm.trans bq)) hd hmodel

/-- Exclude A₈, PSL₄(2), and PSL₅(2) for the actual relative component,
without assuming that the smaller component image is quasisimple. -/
theorem relative_not_higher_binary
    {H B K P : Subgroup G} (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) :
    ¬ HigherBinaryCarrier (K ⧸ pCore 2 K) := by
  intro hmodel
  obtain ⟨P₀,hP₀⟩ := hP
  have hPH : P ≤ H := hP₀ ▸ map_subtype_le (P₀ : Subgroup H)
  have hBH : B ≤ H := hBK.trans hK.1
  have hlocal : B.subgroupOf H ∈ localCComponents P₀ := by
    have hh := (Chapter1.mem_LIn_iff_subgroupOf hPH hBH).mp ⟨hBH,hB⟩
    have he : P.subgroupOf H = (P₀ : Subgroup H) := by
      rw [←hP₀]
      exact comap_map_eq_self_of_injective H.subtype_injective _
    rw [he] at hh
    exact hh.1
  let b := subgroupOfEquivOfLe hBH
  let k := subgroupOfEquivOfLe hK.1
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let kq := QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  obtain ⟨d,hd,hmodel⟩ := higher_binary_model hmodel
  exact local_not_higher_binary P₀ hlocal hK.2 (comap_mono hBK) hn
    (hm.of_mulEquiv bq) (.inr ⟨d,hd,hmodel.of_mulEquiv kq⟩)

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The excluded higher binary rows at both original flag normalizers. -/
theorem flag_not_higher_binary (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) : ¬ HigherBinaryCarrier (K ⧸ pCore 2 K) := by
  have hTV : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) := f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hTV,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTV]⟩
  exact relative_not_higher_binary hs (flag_mem_local_of_model D S f i hm)
    hK hLK S.nonbinary hm

/-- The arbitrary nontrivial subspace clause retains the source's literal
N_T(U) Sylow subgroup and the pointwise action on V₁. -/
theorem subspace_not_higher_binary
    (U : Subgroup G) (hU : U ≠ ⊥) (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) : ¬ HigherBinaryCarrier (K ⧸ pCore 2 K) := by
  let : IsElementaryAbelian 2 (f.Vi 0) :=
    D.centralQuotientPreimage_elementary (c.binarySubspace (f.space 0))
  have htwo : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 (f.Vi 0)).to_le hUV
  have hUL : f.Li 0 ≤ normalizer (U : Set G) :=
    (hfix.trans (centralizer_le hUV)).trans (Subgroup.centralizer_le_normalizer _)
  let P := (T : Subgroup G) ⊓ normalizer (U : Set G)
  have hUP : U ≤ P := le_inf
    (hUV.trans ((D.centralQuotientPreimage_le _).trans D.le_sylow)) U.le_normalizer
  have hcore : U ≤ (f.Li 0 ⊔ P).pCoreIn 2 :=
    le_pCoreIn_of_normalizes htwo (hUP.trans le_sup_right) (sup_le hUL inf_le_right)
  have hlocal := flag_mem_local_of_model D S f 0 hm
  have hlocalP : f.Li 0 ∈ Chapter1.L G P :=
    ⟨hlocal.1.subgroupOf_of_le le_sup_left (sup_le_sup_left inf_le_left _),
      hSyl.restrict le_sup_right (sup_le hUL inf_le_right),
      fun he => hU (bot_unique (he ▸ hcore))⟩
  exact relative_not_higher_binary hSyl hlocalP hK hLK S.nonbinary hm

/-- The containing component supplied by the actual source containment theorem
already avoids every higher binary carrier at either flag normalizer. -/
theorem flag_exists_unique_normal_component_without_higher_binary (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree)) :
    ∃ K : Subgroup G, Source.NormalComponentIn (normalizer (f.Vi i.castSucc : Set G)) K ∧
      f.Li i ≤ K ∧ K ∈ Chapter1.He G ∧
      ¬ HigherBinaryCarrier (K ⧸ pCore 2 K) ∧
      ∀ J : Subgroup G, Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) J →
        f.Li i ≤ J → J = K := by
  obtain ⟨K,hK,hLK,hHe,hu⟩ := flag_exists_unique_normal_component_of_model D S f i hm
  exact ⟨K,hK,hLK,hHe,flag_not_higher_binary D S f i hm hK.1 hLK,hu⟩

/-- The same integrated containment and exclusion for every eligible U ≤ V₁. -/
theorem subspace_exists_unique_normal_component_without_higher_binary
    (U : Subgroup G) (hU : U ≠ ⊥) (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G)) :
    ∃ K : Subgroup G, Source.NormalComponentIn (normalizer (U : Set G)) K ∧
      f.Li 0 ≤ K ∧ ¬ HigherBinaryCarrier (K ⧸ pCore 2 K) ∧
      ∀ J : Subgroup G, Source.ComponentIn (normalizer (U : Set G)) J →
        f.Li 0 ≤ J → J = K := by
  obtain ⟨K,hK,hLK,hu⟩ :=
    subspace_exists_unique_normal_component_of_model D S f U hU hUV hSyl hm hfix
  exact ⟨K,hK,hLK,subspace_not_higher_binary D S f U hU hUV hSyl hm hfix hK.1 hLK,hu⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
