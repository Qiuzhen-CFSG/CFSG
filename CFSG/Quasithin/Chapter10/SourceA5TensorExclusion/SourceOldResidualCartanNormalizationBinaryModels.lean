module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalizationCubicModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients
public import Theory.SpecificGroups.PSL3Two.OuterThreeFree
public import Theory.SpecificGroups.PSL3.OddDegreeProjectiveComparison
/-!
# Excluding all binary rank-two Cartan containers

Restrict the original local A5 section and its normalizing full Sylow to
the actual containing component after the ambient two-core quotient.
Perfectness preserves properness. The proved PSL3 parabolic placement
then forces field order four, a normalization case already discharged.
The two-element-field endpoint has outer group of order two.

Together with the preceding cubic-model sieve this excludes every genuine
Theorem C binary rank-two row in the original nonzero-core reduction.
The local A5 quotient is transported through the literal subgroup maps;
no bare A5 subgroup or stronger module hypothesis is substituted.

Source: Aschbacher--Smith A.3.12, A.3.14(1), A.3.18 and Proposition 9.3.1,
printed pp.47--53,732--733.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceOldResidualCartanNormalizationBinary
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
private theorem binary_parameter
    {X : Type*} [Group X] [Finite X]
    (P : Sylow 2 X) (K J : Subgroup X)
    (hJ : J.IsCComponent) (hK : K ∈ localCComponents P)
    (hKJ : K < J) (hPK : (P : Subgroup X) ≤ normalizer (K : Set X))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (eJ : (J ⧸ pCore 2 J) ≃* PSL(3,F)) : Nat.card F = 4 := by
  let Q := pCore 2 X
  let q := QuotientGroup.mk' Q
  let : Group.IsNilpotent Q := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  have hQK : Q ≤ normalizer (K : Set X) :=
    (pCore_isPGroup.le_sylow_of_normal P).trans hPK
  let : Group.IsPerfect K := FiveLocalFF.SolvableQuotients.local_perfect hK
  let : Group.IsPerfect J := hJ.perfect
  let S := P.mapSurjective (QuotientGroup.mk'_surjective Q)
  let I := J.map q
  let KB := K.map q
  have hIB : KB ≤ I := map_mono hKJ.le
  have hl : KB ∈ localCComponents S :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hK q
  have hSK : (S : Subgroup (X ⧸ Q)) ≤ normalizer (KB : Set (X ⧸ Q)) :=
    (map_mono hPK).trans (le_normalizer_map q)
  have hI : I.IsCComponent := hJ.map_quotient Q
  obtain ⟨R,_,hlocal,_⟩ := exists_local_sylow_normalizing S hl hI.subnormal hIB hSK
  have hproper : KB.subgroupOf I ≠ ⊤ := by
    intro ht
    have he : KB = I := le_antisymm hIB (subgroupOf_eq_top.mp ht)
    have hsup : K ⊔ Q = J ⊔ Q := by
      simpa only [KB,I,q,comap_map_eq,QuotientGroup.ker_mk'] using congrArg (comap q) he
    have hJK : J ≤ K := by
      rw [←map_solvableResidual_sup_eq_of_perfect_normalized K Q hQK]
      apply le_map_solvableResidual_of_isPerfect J (K ⊔ Q)
      rw [hsup]
      exact le_sup_left
    exact hKJ.not_ge hJK
  let ei : I ≃* PSL(3,F) := (cComponentTwoCoreQuotientEquiv hJ).symm.trans eJ
  let : Group.IsSolvable ei.toMonoidHom.ker := by
    rw [ei.toMonoidHom.ker_eq_bot ei.injective]
    infer_instance
  obtain ⟨ekb⟩ := FiveLocalFF.SolvableQuotients.section_map q K hK eK
  let dk : KB.subgroupOf I ≃* KB := subgroupOfEquivOfLe hIB
  let ek : (KB.subgroupOf I ⧸ pCore 2 (KB.subgroupOf I)) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ dk (pCore_map_iso 2 dk)).trans ekb
  have hp : (KB.subgroupOf I).map ei.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hproper
    apply map_injective (f := ei.toMonoidHom) ei.injective
    rw [ht,map_top_of_surjective _ ei.surjective]
  exact (FiveLocalFF.linear_three_five_section_placement hF hn
    (R.mapSurjective (f := ei.toMonoidHom) ei.surjective)
    ((KB.subgroupOf I).map ei.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal ei.toMonoidHom) hp
    (FiveLocalFF.SolvableQuotients.section_map ei.toMonoidHom (KB.subgroupOf I) hlocal ek).some).1
end CFSG.Quasithin.Chapter10.SourceOldResidualCartanNormalizationBinary
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
/-- The literal local A5 section excludes every remaining binary PSL3 container. -/
theorem cartan_container_not_binary_three
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (J : Subgroup G) (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hKJ : (pResidual 2 H).map H.subtype < J)
    (hout : ¬ IsPGroup 2 (MulAut.Outer (J ⧸ pCore 2 J)))
    (hfour : ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 4)
    (n : ℕ) (hn : 0 < n) :
    ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 (2 ^ n) := by
  rintro ⟨F,_,_,hF,⟨a⟩⟩
  by_cases hlarge : 1 < n
  · let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let N := normalizer (m.tensorLine : Set G)
    let K0 := (pResidual 2 H).map H.subtype
    have hKN : K0 ≤ N := hKJ.le.trans hJU
    let P := T.subtype m.tensorLine_normalized
    let K := K0.subgroupOf N
    let JN := J.subgroupOf N
    have hlocal : K ∈ localCComponents P := SourceEmbeddings.local_restrict
      (source_hstar_residual_mem_local_of_a5 hH eK).1 hKN
    have hKJN : K < JN := by
      refine lt_iff_le_not_ge.mpr ⟨comap_mono hKJ.le,?_⟩
      intro hh
      apply hKJ.not_ge
      have hm := map_mono (f := N.subtype) hh
      rwa [map_subgroupOf_eq_of_le hJU,map_subgroupOf_eq_of_le hKN] at hm
    have hPK : (P : Subgroup N) ≤ normalizer (K : Set N) := by
      rw [←subgroupOf_normalizer_eq hKN]
      exact comap_mono (hH.1.1.2.trans (le_normalizer_embedded_pResidual 2 H))
    let b : JN ≃* J := subgroupOfEquivOfLe hJU
    let eJN : (JN ⧸ pCore 2 JN) ≃* PSL(3,F) :=
      (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans a
    let k : K ≃* K0 := subgroupOfEquivOfLe hKN
    let eKN : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) :=
      (QuotientGroup.congr _ _ k (pCore_map_iso 2 k)).trans eK
    have hcard := SourceOldResidualCartanNormalizationBinary.binary_parameter
      P K JN hJ hlocal hKJN hPK eKN hF hlarge eJN
    exact hfour ⟨F,inferInstance,inferInstance,hcard,⟨a⟩⟩
  · have he : n = 1 := by omega
    subst n
    let b := a.trans (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv
      hF (by decide : Odd 1)).symm
    have ho : IsPGroup 2 (MulAut.Outer (Matrix.SpecialLinearGroup (Fin 3) F)) :=
      IsPGroup.of_card (n := 1) (Matrix.PSL3Two.card_outer_of_card_two (by simpa using hF))
    exact hout (ho.of_injective (MulAut.outerCongr b).toMonoidHom (MulAut.outerCongr b).injective)

/-- The original nonzero-core reduction excludes every binary rank-two row
with the proper local A5 section and full Sylow retained. -/
theorem nonzero_core_cartan_normalization_rank_two_excluded
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hcore : pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) ∨
    ∃ J : Subgroup G,
      J ≤ normalizer (m.tensorLine : Set G) ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal ∧
      (pResidual 2 H).map H.subtype < J ∧
      A ≤ normalizer (J : Set G) ∧
      J ≤ centralizer (m.tensorLine : Set G) ∧
      J.pCoreIn 2 ≤ (T : Subgroup G) ∧
      A ⊓ J = B ∧ primeRank 3 J ≤ 2 ∧
      ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 4 ∧
      Nat.Coprime 3 (Nat.card (center (J ⧸ pCore 2 J))) ∧
      (IsQuasisimple (J ⧸ pCore 2 J) →
        IsSimpleGroup (J ⧸ pCore 2 J) ∧ center (J ⧸ pCore 2 J) = ⊥ ∧
        ChapterA.Section02.IsTheoremCModel (J ⧸ pCore 2 J) ∧
        ¬ IsPGroup 2 (MulAut.Outer (J ⧸ pCore 2 J)) ∧
        (∀ n : ℕ, 0 < n →
          ¬ Triality.Standard.IsTrialityGroupAt (2 ^ n) (J ⧸ pCore 2 J)) ∧
        ∀ n : ℕ, ¬ ChapterA.Section02.IsTheoremCRankTwoModel (J ⧸ pCore 2 J) n) := by
  obtain hAK | ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,hpsl,hz3,hqs⟩ :=
    m.nonzero_core_cartan_normalization_binary_sieve hH hlarge
      A B hAB hA9 hAe hB3 hBK hBC hcore
  · exact Or.inl hAK
  refine Or.inr ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,hpsl,hz3,?_⟩
  intro hq
  let := hq
  let := hAe
  obtain ⟨hs,hz,hm,hout,htrial,hrank⟩ := hqs hq
  obtain ⟨eK⟩ := m.old_residual_a5 hH hlarge
  refine ⟨hs,hz,hm,hout,htrial,?_⟩
  intro n hmodel
  have hn : 0 < n := by cases hmodel <;> omega
  exact m.cartan_container_not_binary_three hH eK J hJU hJ hKJ hout hpsl n hn
    (hrank n hmodel)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
