module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.SimpleCatalogue
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveSporadicModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients
public import Theory.GroupAction.SymmetricSixSmallSection
public import Theory.Mathieu.M12.SmallParabolicPair.FirstCore.Order
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# The small Mathieu exclusions in the relative-component catalogue

The actual orders of M₁₁ and M₁₂ force field four for a nonbinary
PSL₂ section modulo its own two-core. A trivial smaller two-core would
make the full normalizing Sylow act faithfully on A₅, contradicting its
order. A nontrivial core places the subgroup and the same Sylow in a
maximal two-local. In M₁₁, the semidihedral normal-elementary calculation
identifies this local with an involution centralizer of order 48. In M₁₂,
the four native local possibilities have no factor five: the two
parabolics have order 192, and each remaining elementary normalizer has
self-centralizing kernel of order at most eight. Thus neither carrier
admits the required smaller component.

Restriction to the containing component and its literal two-core quotient
preserves the smaller subgroup's own core and the original Sylow actor.
The applications cover both flag normalizers and every eligible nontrivial
U ≤ V₁. Applied to SimpleCatalogue's source-derived reduction, these
exclusions leave only M₂₄ and Held in the simple-quotient branch. These
remaining models are explicit proof debt, not source alternatives.
The covers, nonquasisimple cases, refinements and triangle remain with
qt-d-1222-natural-relative-components. The preceding flag markings and
line action belong to qt-d-1222-natural-flag-cartan, with discharge by
qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith A.3.12 and 11.1.1, printed pp.47--48,761,
combined manuscript of 1 March 2004. The imported Mathieu carriers and
native local certificates retain their source attribution and licenses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.ChapterA.Section03
open CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
variable {G : Type*} [Group G] [Finite G]

private theorem normalizer_not_five (E : Subgroup G) (he : IsPGroup 2 E)
    (hc : Nat.card E ≤ 8) (hC : centralizer (E : Set G) = E) :
    ¬ 5 ∣ Nat.card (normalizer (E : Set G)) := by
  let a := E.normalizerMonoidHom
  have hk : a.ker = E.subgroupOf (normalizer (E : Set G)) := by
    rw [normalizerMonoidHom_ker,hC]
  have hck : Nat.card a.ker = Nat.card E := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe E.le_normalizer).toEquiv]
  have hnot : ¬ 5 ∣ Nat.card E := by
    obtain ⟨n,hn⟩ := he.exists_card_eq
    rw [hn]
    exact fun h => (by decide : ¬ 5 ∣ 2) ((by decide : Nat.Prime 5).dvd_of_dvd_pow h)
  intro h
  rw [← a.ker.card_mul_index,index_ker] at h
  rcases (by decide : Nat.Prime 5).dvd_mul.mp h with h | h
  · exact hnot (hck ▸ h)
  · exact MulAut.not_five_dvd_card_of_twoGroup_card_le_eight he hc
      (h.trans a.range.card_subgroup_dvd_card)

private theorem m11_maximal_five_free :
    ∃ S : Sylow 2 Sporadic.Mathieu.M11, ∀ N : Subgroup Sporadic.Mathieu.M11,
      IsMaximalTwoLocal N → (S : Subgroup Sporadic.Mathieu.M11) ≤ N →
      ¬ 5 ∣ Nat.card N := by
  open Sporadic.Mathieu in
  obtain ⟨T,a,b,ha,hb,hc,hg⟩ := m11_exists_semidihedral_sylow
  refine ⟨T,?_⟩
  intro N hN hTN
  obtain ⟨R,hR,hn,he,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le T hN hTN
  let := hn
  let := he
  rw [Semidihedral.normal_elementary_eq_of_order_sixteen a b ha hb hc hg R hR,
    MonoidHom.map_zpowers] at hNR
  have hz : orderOf (((a^4 : T) : Sporadic.Mathieu.M11)) = 2 := by
    rw [orderOf_coe,orderOf_pow,ha]
    norm_num
  change N = normalizer (zpowers (((a^4 : T) : Sporadic.Mathieu.M11)) : Set Sporadic.Mathieu.M11) at hNR
  rw [normalizer_zpowers_eq_centralizer_of_order_two _ hz] at hNR
  rw [hNR]
  open Sporadic.Mathieu in
  obtain ⟨g,hg⟩ := isConj_iff.mp (m11_involution_isConj_generatorA _ hz)
  let f := MulAut.conj g
  have hf : f (((a^4 : T) : Sporadic.Mathieu.M11)) = Sporadic.Mathieu.m11GeneratorAInM11 := hg
  have hmap := CentralizerSmallKernelTransport.map_centralizer f (((a^4 : T) : Sporadic.Mathieu.M11))
  rw [hf] at hmap
  have heq := card_map_of_injective (f := f.toMonoidHom) (K := centralizer ({((a^4 : T) : Sporadic.Mathieu.M11)} : Set Sporadic.Mathieu.M11)) f.injective
  rw [hmap] at heq
  change Nat.card Sporadic.Mathieu.m11InvolutionCentralizer = _ at heq
  rw [Sporadic.Mathieu.m11_involutionCentralizer_card] at heq
  rw [←heq]
  decide

private theorem m12_maximal_five_free :
    ∃ S : Sylow 2 Sporadic.Mathieu.M12, ∀ N : Subgroup Sporadic.Mathieu.M12,
      IsMaximalTwoLocal N → (S : Subgroup Sporadic.Mathieu.M12) ≤ N →
      ¬ 5 ∣ Nat.card N := by
  open Sporadic.Mathieu.M12SmallPair in
  refine ⟨commonSylow,?_⟩
  intro N hN hSN
  open Sporadic.Mathieu.M12SmallPair in
  rcases EvenLocal.maximal_local_cases N hN hSN with rfl | rfl | rfl | rfl
  · rw [Sporadic.Mathieu.M12SmallPair.card_firstParabolic]
    decide
  · rw [Sporadic.Mathieu.M12SmallPair.card_secondParabolic]
    decide
  · apply normalizer_not_five _ (IsElementaryAbelian.isPGroup 2 _) _
      Sporadic.Mathieu.M12SmallPair.EvenLocal.centralizer_pure
    exact (primeRank_le_iff_elementary_card_le _).mp
      Sporadic.Mathieu.m12_twoRank_le_three _ inferInstance
  · exact normalizer_not_five _ (IsElementaryAbelian.isPGroup 2 _)
      Sporadic.Mathieu.M12SmallPair.card_elementary.le
      Sporadic.Mathieu.M12SmallPair.centralizer_elementary_eq

omit [Finite G] in
private theorem section_parameter (B : Subgroup G) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hc : Nat.card G = 7920 ∨ Nat.card G = 95040) : n = 2 := by
  have hv := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
  rw [binary_card hm] at hv
  have hp : 2^n ∣ Nat.card G := (dvd_mul_right _ _).trans hv
  have hb : n < 7 := by
    by_contra! h
    have hh := (show 2^7 ∣ 2^n from pow_dvd_pow 2 h).trans hp
    rcases hc with hc | hc <;> rw [hc] at hh <;> norm_num at hh
  interval_cases n <;> norm_num at hn ⊢ <;>
    rcases hc with hc | hc <;> norm_num [hc] at hv

private theorem not_local_five (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (he : IsEvenCharacteristicAt S) (h16 : 16 ∣ Nat.card G)
    (hN : ∀ N : Subgroup G, IsMaximalTwoLocal N → (S : Subgroup G) ≤ N → ¬ 5 ∣ Nat.card N)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  by_cases hc : pCore 2 B = ⊥
  · let e : B ≃* alternatingGroup (Fin 5) := QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hc).symm.trans eB)
    exact SourceEmbeddings.AlternatingFive.not_sixteen_dvd_of_evenCharacteristic S he hl hn e h16
  · obtain ⟨N,hN',hBN,hSN⟩ := SourceEmbeddings.FiveLocalFF.SolvableQuotients.exists_maximal_two_local S B hn hc
    exact hN N hN' hSN ((SourceEmbeddings.FiveLocalFF.SolvableQuotients.five_dvd_card B eB).trans
      (card_dvd_of_le hBN))

@[expose] def SmallMathieuCarrier (A : Type*) [Group A] : Prop :=
  Nonempty (A ≃* Sporadic.Mathieu.M11) ∨ Nonempty (A ≃* Sporadic.Mathieu.M12)

private theorem not_local_of_small_model {M : Type*} [Group M] [Finite M]
    (e : G ≃* M) (horder : Nat.card M = 7920 ∨ Nat.card M = 95040)
    (he : IsEvenCharacteristic M)
    (hmax : ∃ T : Sylow 2 M, ∀ N : Subgroup M,
      IsMaximalTwoLocal N → (T : Subgroup M) ≤ N → ¬ 5 ∣ Nat.card N)
    (S : Sylow 2 G) (B : Subgroup G) (hl : B ∈ localCComponents S)
    (hnorm : (S : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) : False := by
  have hn2 := section_parameter B hn hm (by rwa [Nat.card_congr e.toEquiv])
  obtain ⟨F,_,_,hF,⟨b⟩⟩ := hm
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (show Nat.card F = 4 by simpa [hn2] using hF)
  let eB := b.trans a
  obtain ⟨T,hmax⟩ := hmax
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M Q T
  let f := e.trans (MulAut.conj g)
  have hS : (S : Subgroup G).map f.toMonoidHom = (T : Subgroup M) := by
    have h := congrArg (fun P : Sylow 2 M => (P : Subgroup M)) hg
    change ((S : Subgroup G).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at h
    have hf : f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by ext x; rfl
    rw [hf,←map_map]
    exact h
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot f.injective]
    infer_instance
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom
  have hn' := (map_mono (f := f.toMonoidHom) hnorm).trans (B.le_normalizer_map f.toMonoidHom)
  rw [hS] at hl' hn'
  exact not_local_five T (B.map f.toMonoidHom) hl' hn' (he T)
    (by rcases horder with h | h <;> rw [h] <;> decide) hmax
    (SourceEmbeddings.FiveLocalFF.SolvableQuotients.section_map f.toMonoidHom B hl eB).some

/-- Neither small Mathieu carrier contains the normalized full-Sylow
local component with a nonbinary binary-rank-one two-core section. -/
theorem not_local_small_mathieu
    (S : Sylow 2 G) (B : Subgroup G) (hl : B ∈ localCComponents S)
    (hnorm : (S : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hmodel : SmallMathieuCarrier G) : False := by
  rcases hmodel with hmodel | hmodel
  all_goals obtain ⟨e⟩ := hmodel
  · exact not_local_of_small_model e (.inl Sporadic.Mathieu.m11_order)
      MainConverse.m11_evenCharacteristic m11_maximal_five_free S B hl hnorm hn hm
  · exact not_local_of_small_model e (.inr Sporadic.Mathieu.m12_order)
      MainConverse.m12_evenCharacteristic m12_maximal_five_free S B hl hnorm hn hm

private theorem local_not_small_mathieu
    (P : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents P) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hPB : (P : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hmodel : SmallMathieuCarrier (K ⧸ pCore 2 K)) : False := by
  obtain ⟨R,hPR,hR⟩ := SourceEmbeddings.exists_local_sylow_restriction P hB hBK hK.subnormal
  let C := B.subgroupOf K
  have hnR : (R : Subgroup K) ≤ normalizer (C : Set K) := by
    rw [hPR]
    intro x hx
    apply mem_normalizer_iff.mpr
    intro b
    exact mem_normalizer_iff.mp (hPB hx) (b : G)
  let q := QuotientGroup.mk' (pCore 2 K)
  let : Group.IsNilpotent (pCore 2 K) := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  have hk : IsPGroup 2 (q.subgroupMap C).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let b := subgroupOfEquivOfLe hBK
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let a := (q.subgroupMap C).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective C) hk
  exact not_local_small_mathieu (R.mapSurjective (QuotientGroup.mk'_surjective _))
    (C.map q) (Chapter1.Section02.localCComponents_map_of_solvable_ker hR q)
    ((map_mono (f := q) hnR).trans (C.le_normalizer_map q)) hn
    (hm.of_mulEquiv (a.symm.trans bq)) hmodel

/-- The actual smaller two-core and relative Sylow are retained when
excluding M₁₁ and M₁₂ for the containing component. -/
theorem relative_not_small_mathieu
    {H B K P : Subgroup G} (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    (hPB : P ≤ normalizer (B : Set G)) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) :
    ¬ SmallMathieuCarrier (K ⧸ pCore 2 K) := by
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
  have hnP : (P₀ : Subgroup H) ≤ normalizer (B.subgroupOf H : Set H) := by
    intro x hx
    have hxP : (x : G) ∈ P := hP₀ ▸ mem_map_of_mem H.subtype hx
    apply mem_normalizer_iff.mpr
    intro b
    exact mem_normalizer_iff.mp (hPB hxP) (b : G)
  let b := subgroupOfEquivOfLe hBH
  let k := subgroupOfEquivOfLe hK.1
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let kq := QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  apply local_not_small_mathieu P₀ hlocal hK.2 (comap_mono hBK) hnP hn
    (hm.of_mulEquiv bq)
  rcases hmodel with hmodel | hmodel
  all_goals obtain ⟨e⟩ := hmodel
  · exact .inl ⟨kq.trans e⟩
  · exact .inr ⟨kq.trans e⟩

/-- In the simple-quotient branch, the source-derived catalogue now leaves
only the two large sporadic exclusions as explicit proof debt. -/
theorem relative_simple_source_without_small_mathieu
    {H B K P : Subgroup G} (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    (hPB : P ≤ normalizer (B : Set G)) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    [IsSimpleGroup (K ⧸ pCore 2 K)] :
    ComponentAlternative B K n ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Held.He) := by
  rcases relative_simple_source hH hP hB hK hBK hPB hn hm with h | h
  · exact .inl h
  rcases h with h | h | h | h
  · exact (relative_not_small_mathieu hP hB hK hBK hPB hn hm (.inl h)).elim
  · exact (relative_not_small_mathieu hP hB hK hBK hPB hn hm (.inr h)).elim
  · exact .inr (.inl h)
  · exact .inr (.inr h)

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The excluded small Mathieu rows at both original flag normalizers. -/
theorem flag_not_small_mathieu (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) : ¬ SmallMathieuCarrier (K ⧸ pCore 2 K) := by
  have hTV : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) := f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hTV,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTV]⟩
  exact relative_not_small_mathieu hs (flag_mem_local_of_model D S f i hm)
    hK hLK (f.sylow_normalizes_Li i) S.nonbinary hm

/-- The arbitrary nontrivial subspace clause retains the source's literal
N_T(U) Sylow subgroup and the pointwise action on V₁. -/
theorem subspace_not_small_mathieu
    (U : Subgroup G) (hU : U ≠ ⊥) (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) : ¬ SmallMathieuCarrier (K ⧸ pCore 2 K) := by
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
  exact relative_not_small_mathieu hSyl hlocalP hK hLK (inf_le_left.trans (f.sylow_normalizes_Li 0)) S.nonbinary hm

/-- The source-derived simple-carrier reduction at both original flag normalizers. -/
theorem flag_simple_source_without_small_mathieu (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) [IsSimpleGroup (K ⧸ pCore 2 K)] :
    ComponentAlternative (f.Li i) K S.field.degree ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Held.He) := by
  have hTV : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) := f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hTV,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTV]⟩
  exact relative_simple_source_without_small_mathieu
    (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal i.castSucc)) hs
    (flag_mem_local_of_model D S f i hm) hK hLK (f.sylow_normalizes_Li i) S.nonbinary hm

/-- The same source-derived catalogue reduction for arbitrary nontrivial U ≤ V₁. -/
theorem subspace_simple_source_without_small_mathieu
    (U : Subgroup G) (hU : U ≠ ⊥) (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) [IsSimpleGroup (K ⧸ pCore 2 K)] :
    ComponentAlternative (f.Li 0) K S.field.degree ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Held.He) := by
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
  exact relative_simple_source_without_small_mathieu (S.source.simpleQTKE.twoLocal_sqtk ⟨U,hU,htwo,rfl⟩)
    hSyl hlocalP hK hLK (inf_le_left.trans (f.sylow_normalizes_Li 0)) S.nonbinary hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
