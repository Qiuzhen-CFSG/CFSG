module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveSectionTernarySieve
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeFiveSection
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalizationBinaryModels
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalizationUnitaryControl
/-!
# The complete quasisimple Cartan-container sieve

For the original Chapter 10 Cartan and embedded old residual, the remaining
quasisimple containing quotient lies in the actual Theorem C catalogue.
Retain its proper local A5 section through the ambient two-core quotient,
and apply the proved catalogue and odd ternary parameter theorems. The
parameter-five linear row has two-group outer automorphisms; the unitary
row is the completed PSU3(5) normalization case. Thus any surviving
proper containing quotient is nonquasisimple.

Every subgroup, quotient map and full Sylow intersection is the original
source construction. Source: Aschbacher--Smith A.3.14, A.3.18 and
Proposition 9.3.1, printed pp.47--53,732--733.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ChapterA.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
private theorem marked_image
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (J : Subgroup G) (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hKJ : (pResidual 2 H).map H.subtype < J) :
    let N := normalizer (m.tensorLine : Set G)
    let K := ((pResidual 2 H).map H.subtype).subgroupOf N
    let JN := J.subgroupOf N
    let q := QuotientGroup.mk' (pCore 2 N)
    let I := JN.map q
    let C := (K.map q).subgroupOf I
    Nonempty (I ≃* (J ⧸ pCore 2 J)) ∧
      ∃ S : Sylow 2 I,
        (S : Subgroup I) =
          (((T.subtype m.tensorLine_normalized).mapSurjective
            (QuotientGroup.mk'_surjective (pCore 2 N))) : Subgroup (N ⧸ pCore 2 N)).subgroupOf I ∧
        C ∈ localCComponents S ∧ (S : Subgroup I) ≤ normalizer (C : Set I) ∧
        C ≠ ⊤ ∧ Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) := by
  intro N K JN q I C
  let K0 := (pResidual 2 H).map H.subtype
  have hKN : K0 ≤ N := hKJ.le.trans hJU
  let P := T.subtype m.tensorLine_normalized
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
  let k : K ≃* K0 := subgroupOfEquivOfLe hKN
  let eKN : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ k (pCore_map_iso 2 k)).trans eK
  let j : JN ≃* J := subgroupOfEquivOfLe hJU
  let d : I ≃* (J ⧸ pCore 2 J) := (cComponentTwoCoreQuotientEquiv hJ).symm.trans
    (QuotientGroup.congr _ _ j (pCore_map_iso 2 j))
  exact ⟨⟨d⟩,SourceEmbeddings.proper_five_section_in_containing_image
    P K JN hJ hlocal hKJN hPK eKN⟩

/-- Every remaining quasisimple container is an odd prime-field ternary group.
The smaller local A5 section is retained in the actual ambient two-core image. -/
theorem cartan_quasisimple_container_isOddTernary
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (J : Subgroup G) (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hKJ : (pResidual 2 H).map H.subtype < J)
    [IsQuasisimple (J ⧸ pCore 2 J)] [IsSimpleGroup (J ⧸ pCore 2 J)]
    (hm : ChapterA.Section02.IsTheoremCModel (J ⧸ pCore 2 J))
    (hout : ¬ IsPGroup 2 (MulAut.Outer (J ⧸ pCore 2 J)))
    (hrank : ∀ n, ¬ ChapterA.Section02.IsTheoremCRankTwoModel (J ⧸ pCore 2 J) n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      (ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 p ∨ ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 p) := by
  obtain ⟨⟨d⟩,S,_,hC,_,hproper,⟨eC⟩⟩ := m.marked_image hH eK J hJU hJ hKJ
  let : IsSimpleGroup _ := d.isSimpleGroup
  let : IsQuasisimple _ := IsQuasisimple.of_mulEquiv d.symm
  have hmodel := hm.of_mulEquiv d
  have houter : ¬ IsPGroup 2 (MulAut.Outer _) := fun ho => hout (ho.of_equiv (MulAut.outerCongr d))
  obtain ⟨p,hp,ho,hmod⟩ := SourceEmbeddings.five_section_nonordinary_model_is_odd_ternary
    S _ hC hproper eC hmodel houter (fun n hn => hrank n (hn.of_mulEquiv d.symm))
  exact ⟨p,hp,ho,hmod.imp (fun h => h.of_mulEquiv d.symm) (fun h => h.of_mulEquiv d.symm)⟩

/-- All remaining source rows are nonquasisimple or odd ternary of prime
parameter distinct from five. The PSU3(5) and PSL3(5) rows are discharged. -/
theorem nonzero_core_cartan_normalization_remaining_odd_ternary
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
      Nat.Coprime 3 (Nat.card (center (J ⧸ pCore 2 J))) ∧
      (IsQuasisimple (J ⧸ pCore 2 J) →
        IsSimpleGroup (J ⧸ pCore 2 J) ∧
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ≠ 5 ∧
          (ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 p ∨
            ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 p)) := by
  obtain hAK | ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,hpsl,hz3,hqs⟩ :=
    m.nonzero_core_cartan_normalization_rank_two_excluded hH hlarge
      A B hAB hA9 hAe hB3 hBK hBC hcore
  · exact .inl hAK
  obtain ⟨eK⟩ := m.old_residual_a5 hH hlarge
  by_cases hu : ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 5
  · let := hAe
    exact .inl (m.cartan_normalizes_old_residual_of_unitary_three_container hH eK A J
      hAB hA9 (by rw [hAJB,hB3]) hJU hJ hnJ hKJ.le hu)
  refine .inr ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,hz3,?_⟩
  intro hq
  let := hq
  obtain ⟨hs,hz,hm,hout,_,hrank⟩ := hqs hq
  let := hs
  obtain ⟨p,hp,ho,hmodel⟩ := m.cartan_quasisimple_container_isOddTernary hH eK J
    hJU hJ hKJ hm hout hrank
  refine ⟨hs,p,hp,ho,?_,hmodel⟩
  intro he
  subst p
  exact hmodel.elim
    (fun h => hout (SourceEmbeddings.linear_three_five_outer_two h)) hu

/-- The proved odd ternary section theorem closes the quasisimple remainder.
The remaining component retains every original source marking. -/
theorem nonzero_core_cartan_normalization_nonquasisimple
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
      Nat.Coprime 3 (Nat.card (center (J ⧸ pCore 2 J))) ∧
      ¬ IsQuasisimple (J ⧸ pCore 2 J) := by
  obtain hAK | ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,hz3,hqs⟩ :=
    m.nonzero_core_cartan_normalization_remaining_odd_ternary hH hlarge
      A B hAB hA9 hAe hB3 hBK hBC hcore
  · exact .inl hAK
  refine .inr ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,hz3,?_⟩
  intro hq
  obtain ⟨_,p,hp,ho,hp5,hm⟩ := hqs hq
  obtain ⟨eK⟩ := m.old_residual_a5 hH hlarge
  obtain ⟨⟨d⟩,S,_,hC,hSC,_,eC⟩ := m.marked_image hH eK J hJU hJ hKJ
  exact hp5 (SourceEmbeddings.odd_three_five_section_parameter S _ hC hSC eC hp ho
    (hm.imp (fun h => h.of_mulEquiv d) (fun h => h.of_mulEquiv d)))

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
