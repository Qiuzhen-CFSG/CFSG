module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Membership
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Statements
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximality
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Parameters
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.PrimePSL2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuadraticPSL2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankOne
public import Theory.SpecificGroups.AlternatingFiveCore
public import Theory.SpecificGroups.PSL2.OddPerfectCore

/-!
# Rank-one relative-component embeddings

The binary rank-one row gives equality by the full-Sylow overgroup theorem.
For odd prime and prime-square rows, apply the proper-subcomponent embedding
results to the literal ambient two-core quotient. The image of the smaller
component is respectively A₅ or PSL₂(p). Its intrinsic two-core is trivial,
so comparison with the original PSL₂(2ⁿ) quotient forces n = 2; the square
row further forces p = 5. The prime row retains both source congruences.

The consumers apply this argument inside the actual flag normalizers, and
inside N_G(U) for nontrivial U ≤ V₁ with N_T(U) Sylow in N_G(U). Normality
and the quotient maps are relative throughout. These results prove the
rank-one branches of the embedding list; the remaining carrier branches
are still owned by the relative-components assembly task.

The preceding flag quotient and pointwise-action premises come from
qt-d-1222-natural-flag-cartan and are discharged by
qt-d-1222-natural-local-geometry. Refinement.RankOne applies these results
to the first-normalizer refinement without an embedding-list premise.

Source: Aschbacher--Smith, A.3.12(8), printed pp.47--48, and 11.1.1--11.1.2,
printed pp.761--762, combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.ChapterA.Section03
open CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
variable {G : Type*} [Group G] [Finite G]

private noncomputable def quotientEquivImage {B : Subgroup G} {A : Type*} [Group A]
    (e : B.map (QuotientGroup.mk' (pCore 2 G)) ≃* A) (hz : pCore 2 A = ⊥) :
    (B ⧸ pCore 2 B) ≃* A := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hk : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  exact (MonoidHom.quotientPCoreEquivOfSurjective (q.subgroupMap B)
    (q.subgroupMap_surjective B) hk).trans
      ((QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
        ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot))

/-- A proper prime-field row forces degree two and the source prime congruences. -/
theorem proper_prime_rank_one_parameters
    (P : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents P) (hK : K.IsCComponent) (hBK : B < K)
    {n p : ℕ} (hn : 0 < n)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p) :
    n = 2 ∧ Source.ExceptionalPrime p := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let := pCore_isNilpotent (p := 2) (G := G)
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))
  have hb : B.map q ∈ localCComponents Q :=
    localCComponents_map_of_solvable_ker hB q
  have hne : B.map q ≠ K.map q := fun he => hBK.ne
    (MovedMaximality.eq_of_twoCore_images_eq P hB hK hBK.le he)
  obtain ⟨⟨_,_,hsq,h8⟩,⟨e⟩⟩ := SourceEmbeddings.proper_primePSL2_models Q hb
    (hK.map_quotient _) (map_mono hBK.le) hne hp ho
    (hmodel.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK).symm)
  have hn2 := binary_parameter_of_alternating_five hn hsmall
    ⟨quotientEquivImage e alternatingGroup.five_twoCore_eq_bot⟩
  refine ⟨hn2,hp,?_,h8⟩
  have hbound := Nat.mod_lt p (by decide : 0 < 5)
  interval_cases h : p % 5 <;> simp_all [Nat.pow_mod]

/-- A proper quadratic-field row forces degree two and prime parameter five. -/
theorem proper_quadratic_rank_one_parameters
    (P : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents P) (hK : K.IsCComponent) (hBK : B < K)
    {n p : ℕ} (hn : 1 < n)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (p ^ 2)) :
    n = 2 ∧ p = 5 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let := pCore_isNilpotent (p := 2) (G := G)
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))
  have hb : B.map q ∈ localCComponents Q :=
    localCComponents_map_of_solvable_ker hB q
  have hne : B.map q ≠ K.map q := fun he => hBK.ne
    (MovedMaximality.eq_of_twoCore_images_eq P hB hK hBK.le he)
  obtain ⟨hgt,hm⟩ := SourceEmbeddings.proper_quadraticPSL2_models Q hb
    (hK.map_quotient _) (map_mono hBK.le) hne hp ho
    (hmodel.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK).symm)
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let A := B.map q
  let a : A.subgroupOf (A ⊔ (Q : Subgroup (G ⧸ pCore 2 G))) ≃* A :=
    subgroupOfEquivOfLe le_sup_left
  let := hb.perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := a.toMonoidHom) a.surjective
  have hzero : pCore 2 A = ⊥ := by
    apply bot_unique
    intro x hx
    exact e.map_eq_one_iff.mp
      (Theory.PSL2.odd_perfect_hom_twoCore_le_ker (hF.symm ▸ ho) e.toMonoidHom hx)
  let aQ : (B ⧸ pCore 2 B) ≃* A := quotientEquivImage (MulEquiv.refl _) hzero
  exact binary_odd_prime_parameters hn hsmall hp ho hgt
    ⟨F,inferInstance,inferInstance,hF,⟨aQ.trans e⟩⟩

open scoped MatrixGroups in
/-- A binary rank-one quotient admits no proper local C-component under the full Sylow. -/
theorem eq_of_binary_rank_one
    (P : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents P) (hK : K.IsCComponent) (hBK : B ≤ K)
    {m : ℕ} (hm : 1 < m)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ m)) : B = K := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show (4 : ℕ) = 2 ^ 2 from rfl).le.trans
      (Nat.pow_le_pow_right (by decide) hm)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
  let : IsSimpleGroup (K ⧸ pCore 2 K) := e.isSimpleGroup
  let := hK.perfect
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    rcases (inferInstance : (center (K ⧸ pCore 2 K)).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative (K ⧸ pCore 2 K)
        (center_eq_top_iff.mp ht)).elim
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    { toIsPerfect := inferInstance
      simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  let a := e.trans (BenderSuzuki.ZD.Linear.sl2QuotientEquiv F).symm
  exact SourceEmbeddings.eq_of_rankOne_cover P hB hK hBK
    (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))
    (a.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 K)))

/-- Transport both odd rank-one parameter restrictions through the literal local group H. -/
theorem relative_odd_rank_one_parameters
    {H B K P : Subgroup G}
    (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B < K)
    {n p : ℕ} (hn : 1 < n)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hp : p.Prime) (ho : Odd p) :
    (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p → n = 2 ∧ Source.ExceptionalPrime p) ∧
    (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (p ^ 2) → n = 2 ∧ p = 5) := by
  obtain ⟨P₀, hP₀⟩ := hP
  have hPH : P ≤ H := hP₀ ▸ map_subtype_le (P₀ : Subgroup H)
  have hBH : B ≤ H := hBK.le.trans hK.1
  have hlocal : B.subgroupOf H ∈ localCComponents P₀ := by
    have hh := (Chapter1.mem_LIn_iff_subgroupOf hPH hBH).mp ⟨hBH, hB⟩
    have he : P.subgroupOf H = (P₀ : Subgroup H) := by
      rw [← hP₀]
      exact comap_map_eq_self_of_injective H.subtype_injective _
    rw [he] at hh
    exact hh.1
  have hlt : B.subgroupOf H < K.subgroupOf H := by
    refine lt_of_le_of_ne (comap_mono hBK.le) ?_
    intro he
    apply hBK.ne
    simpa only [map_subgroupOf_eq_of_le hBH, map_subgroupOf_eq_of_le hK.1] using
      congrArg (map H.subtype) he
  let b := subgroupOfEquivOfLe hBH
  let k := subgroupOfEquivOfLe hK.1
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let kq := QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  exact ⟨fun hm => proper_prime_rank_one_parameters P₀ hlocal hK.2 hlt (by omega)
      (hsmall.of_mulEquiv bq) hp ho (hm.of_mulEquiv kq),
    fun hm => proper_quadratic_rank_one_parameters P₀ hlocal hK.2 hlt hn
      (hsmall.of_mulEquiv bq) hp ho (hm.of_mulEquiv kq)⟩

/-- Binary rank-one non-enlargement inside the relative local group H. -/
theorem relative_eq_of_binary_rank_one
    {H B K P : Subgroup G}
    (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    {m : ℕ} (hm : 1 < m)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ m)) : B = K := by
  obtain ⟨P₀, hP₀⟩ := hP
  have hPH : P ≤ H := hP₀ ▸ map_subtype_le (P₀ : Subgroup H)
  have hBH : B ≤ H := hBK.trans hK.1
  have hlocal : B.subgroupOf H ∈ localCComponents P₀ := by
    have hh := (Chapter1.mem_LIn_iff_subgroupOf hPH hBH).mp ⟨hBH, hB⟩
    have he : P.subgroupOf H = (P₀ : Subgroup H) := by
      rw [← hP₀]
      exact comap_map_eq_self_of_injective H.subtype_injective _
    rw [he] at hh
    exact hh.1
  let k := subgroupOfEquivOfLe hK.1
  let kq := QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  have he := eq_of_binary_rank_one P₀ hlocal hK.2 (comap_mono hBK) hm
    (hmodel.of_mulEquiv kq)
  simpa only [map_subgroupOf_eq_of_le hBH, map_subgroupOf_eq_of_le hK.1] using
    congrArg (map H.subtype) he

/-- The rank-one branch of 11.1.1, retaining the literal component quotient and local Sylow. -/
theorem relative_component_alternative_of_rank_one
    {H B K P : Subgroup G}
    (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    {n : ℕ} (hn : 1 < n)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hmodel : (∃ m, 1 < m ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ m)) ∨
      ∃ p, p.Prime ∧ Odd p ∧ (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p ∨
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (p ^ 2))) :
    ComponentAlternative B K n := by
  by_cases he : B = K
  · exact .equal he
  rcases hmodel with ⟨m, hm, hk⟩ | ⟨p, hp, ho, hmodel⟩
  · exact .equal (relative_eq_of_binary_rank_one hP hB hK hBK hm hk)
  have h := relative_odd_rank_one_parameters hP hB hK (lt_of_le_of_ne hBK he)
    hn hsmall hp ho
  rcases hmodel with hm | hm
  · obtain ⟨hn2, hp⟩ := h.1 hm
    exact .four hn2 (.primeLinear p hp hm)
  · obtain ⟨hn2, hp⟩ := h.2 hm
    exact .four hn2 (.linearTwentyFive (by simpa [hp] using hm))

variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The actual flag residual supplies the local-family premise for both odd rank-one rows. -/
theorem flag_odd_rank_one_parameters (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i < K) {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p →
      S.field.degree = 2 ∧ Source.ExceptionalPrime p) ∧
    (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (p ^ 2) →
      S.field.degree = 2 ∧ p = 5) := by
  have hT : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) :=
    f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hT, by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hT]⟩
  exact relative_odd_rank_one_parameters hs (flag_mem_local_of_model D S f i hm)
    hK hLK S.nonbinary hm hp ho

/-- Either flag residual equals its containing component in the binary rank-one row. -/
theorem flag_eq_of_binary_rank_one (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) {m : ℕ} (hm' : 1 < m)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ m)) : f.Li i = K := by
  have hT : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) :=
    f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hT, by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hT]⟩
  exact relative_eq_of_binary_rank_one hs (flag_mem_local_of_model D S f i hm)
    hK hLK hm' hmodel

/-- Apply the rank-one embedding branch to both original flag normalizers. -/
theorem flag_component_alternative_of_rank_one (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K)
    (hmodel : (∃ m, 1 < m ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ m)) ∨
      ∃ p, p.Prime ∧ Odd p ∧ (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p ∨
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (p ^ 2))) :
    ComponentAlternative (f.Li i) K S.field.degree := by
  by_cases he : f.Li i = K
  · exact .equal he
  rcases hmodel with ⟨m, hm', hk⟩ | ⟨p, hp, ho, hmodel⟩
  · exact .equal (flag_eq_of_binary_rank_one D S f i hm hK hLK hm' hk)
  have h := flag_odd_rank_one_parameters D S f i hm hK (lt_of_le_of_ne hLK he) hp ho
  rcases hmodel with hk | hk
  · obtain ⟨hn2, hprime⟩ := h.1 hk
    exact .four hn2 (.primeLinear p hprime hk)
  · obtain ⟨hn2, hp5⟩ := h.2 hk
    exact .four hn2 (.linearTwentyFive (by simpa [hp5] using hk))

/-- Apply the same branch to arbitrary nontrivial U ≤ V₁, with the original N_T(U) Sylow condition. -/
theorem subspace_component_alternative_of_rank_one
    (U : Subgroup G) (hU : U ≠ ⊥) (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hmodel : (∃ m, 1 < m ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ m)) ∨
      ∃ p, p.Prime ∧ Odd p ∧ (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p ∨
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (p ^ 2))) :
    ComponentAlternative (f.Li 0) K S.field.degree := by
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
  exact relative_component_alternative_of_rank_one hSyl hlocalP hK hLK
    S.nonbinary hm hmodel

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
