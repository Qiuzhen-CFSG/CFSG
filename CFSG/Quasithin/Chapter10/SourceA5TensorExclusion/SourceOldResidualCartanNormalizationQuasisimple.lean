module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimplePrimeToThreeCenter
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalizationCenterThree
public import Theory.SpecificGroups.Triality.CComponentResidual
public import Theory.GroupTheory.FiniteParabolicTransfer
/-!
# Simple containing quotients and the triality exclusion

The original line normalizer is SQTK. Its actual containing component has
center of order prime to three modulo its two-core. Thus a quasisimple
quotient is simple and belongs to the genuine Theorem C catalogue.

The triality row is excluded using its cubic residual identity in the
literal line normalizer: the full order-nine Cartan plane would lie in the
containing component, contradicting its marked order-three intersection.
No replacement of the old local A5 section by an A5 subgroup is made.

Source: Aschbacher--Smith A.3.6, A.3.18 and Proposition 9.3.1,
printed pp.43--44,51--53,732--733.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
/-- The actual quasisimple containing quotient is a simple Theorem C model. -/
theorem cartan_quasisimple_container_catalogue (J : Subgroup G)
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    [IsQuasisimple (J ⧸ pCore 2 J)]
    (hz : Nat.Coprime 3 (Nat.card (center (J ⧸ pCore 2 J)))) :
    IsSimpleGroup (J ⧸ pCore 2 J) ∧ center (J ⧸ pCore 2 J) = ⊥ ∧
      ChapterA.Section02.IsTheoremCModel (J ⧸ pCore 2 J) := by
  let N := normalizer (m.tensorLine : Set G)
  have hN := D.simpleQTKE.twoLocal_sqtk (show IsTwoLocal N from
    ⟨m.tensorLine,m.tensorLine_ne_bot,IsPGroup.of_card (n := 2) m.card_tensorLine,rfl⟩)
  have hJG : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJU)).mp (hN.subgroup (J.subgroupOf N))
  have hQ : IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) := by
    refine ⟨?_,hJG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hJG.stronglyQuasithin p hp ho)
  have hs := ChapterA.Section03.SourceEmbeddings.quasisimple_isSimple_of_center_coprime_three hQ
    (pCore_quotient_pCore_eq_bot 2) hz
  let := hs
  have hz0 : center (J ⧸ pCore 2 J) = ⊥ :=
    (inferInstance : (center (J ⧸ pCore 2 J)).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht))
  exact ⟨hs,hz0,ChapterA.Section02.theoremC_knownSimple hs
    (Group.IsPerfect.not_isMulCommutative _) hQ.stronglyQuasithin hQ.isKGroup⟩
/-- A triality quotient would absorb the full original Cartan plane. -/
theorem cartan_container_not_triality
    (A B J : Subgroup G) [IsElementaryAbelian 3 A]
    (hA9 : Nat.card A = 9) (hB3 : Nat.card B = 3)
    (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hAJB : A ⊓ J = B) [IsQuasisimple (J ⧸ pCore 2 J)]
    (n : ℕ) (hn : 0 < n)
    (a : (J ⧸ pCore 2 J) ≃* Triality.Standard.BinaryCarrier n hn) : False := by
  let N := normalizer (m.tensorLine : Set G)
  let I := J.subgroupOf N
  let C := A.subgroupOf N
  let j : I ≃* J := subgroupOfEquivOfLe hJU
  let b : (I ⧸ pCore 2 I) ≃* (J ⧸ pCore 2 J) :=
    QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
  let : IsQuasisimple (I ⧸ pCore 2 I) := IsQuasisimple.of_mulEquiv b.symm
  have hN := D.simpleQTKE.twoLocal_sqtk (show IsTwoLocal N from
    ⟨m.tensorLine,m.tensorLine_ne_bot,IsPGroup.of_card (n := 2) m.card_tensorLine,rfl⟩)
  have he : I = primeToResidual 3 N :=
    Triality.Standard.cComponent_eq_primeToResidual_three hJ
      (hN.stronglyQuasithin 3 (by decide) (by decide)) n hn (b.trans a)
  have hCI : C ≤ I := he ▸ le_primeToResidual_of_isPGroup
    (IsElementaryAbelian.isPGroup 3 A).comap_subtype
  have hAJ : A ≤ J := by
    intro x hx
    exact hCI (show (⟨x,hAU hx⟩ : N) ∈ C from hx)
  have heq : A = B := (inf_eq_left.mpr hAJ).symm.trans hAJB
  have hc := congrArg (fun K : Subgroup G => Nat.card K) heq
  rw [hA9,hB3] at hc
  omega

/-- The model-predicate version matches the genuine Theorem C triality row. -/
theorem cartan_container_not_triality_model
    (A B J : Subgroup G) [IsElementaryAbelian 3 A]
    (hA9 : Nat.card A = 9) (hB3 : Nat.card B = 3)
    (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hAJB : A ⊓ J = B) [IsQuasisimple (J ⧸ pCore 2 J)]
    (n : ℕ) (hn : 0 < n) :
    ¬ Triality.Standard.IsTrialityGroupAt (2 ^ n) (J ⧸ pCore 2 J) := by
  intro hmodel
  obtain ⟨a⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n hn).mp hmodel
  exact m.cartan_container_not_triality A B J hA9 hB3 hAU hJU hJ hAJB n hn a

/-- The original nonzero-core reduction, with the actual quasisimple quotient
classified by Theorem C and its outer-two and triality rows excluded. -/
theorem nonzero_core_cartan_normalization_quasisimple_sieve
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
        ∀ n : ℕ, 0 < n →
          ¬ Triality.Standard.IsTrialityGroupAt (2 ^ n) (J ⧸ pCore 2 J)) := by
  obtain hAK | ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,hout,hpsl,hz3⟩ :=
    m.nonzero_core_cartan_normalization_remaining_cases_center_three hH hlarge
      A B hAB hA9 hAe hB3 hBK hBC hcore
  · exact Or.inl hAK
  refine Or.inr ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,hpsl,hz3,?_⟩
  intro hq
  let := hq
  let := hAe
  obtain ⟨hs,hz,hm⟩ := m.cartan_quasisimple_container_catalogue J hJU hz3
  exact ⟨hs,hz,hm,fun ho => hout ⟨hq,hz,ho⟩,
    fun n hn => m.cartan_container_not_triality_model A B J hA9 hB3
      (hAB.trans m.borel_normalizes_tensorLine) hJU hJ hAJB n hn⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
