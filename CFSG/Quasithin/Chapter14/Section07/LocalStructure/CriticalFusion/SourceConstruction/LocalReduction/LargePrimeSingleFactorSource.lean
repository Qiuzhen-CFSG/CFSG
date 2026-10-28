module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeSingleThompson
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCoreContainmentSource

/-!
# The original singleton exclusion and remaining simultaneous-cubic branch

Apply the four-dimensional normalizer calculation to the actual canonical
family supplied by the original minimal five-core reduction. In the
singleton case it places Ω₁(T) in R₁. The source-marked L₃(2) fusion then
places it in O₂(LT). Thompson heredity, uniqueness over LT and solvable
Thompson factorization force the original escaping five-core lift into M.
This excludes the singleton case without a new local recognition premise.

Minimality makes the argument apply to any fixed original witness and its
unchanged quotient action. The ambient five-rank bound gives exactly two
canonical factors. Combining this with the full-action exclusion leaves
both endpoint two-cores centralizing the same common eight-group, the
simultaneous-cubic alternative. Its exclusion and the later local
recognition reductions remain to be proved.

The original group, flag, minimal local I, normal five-core X, two-perfect
lift Y and exact quotient kernels are retained throughout.

Source: Aschbacher–Smith, 14.7.6, printed pp.1044–1045, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Chapter12.Section08 CriticalFusion.Source ChapterD ChapterB
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter14.Section06.OddCriticalPair.Selection
open Chapter14.Section04.LargerDimension.LocalAction.Components
open scoped IsMulCommutative
universe u

/-- Apply the singleton-factor argument to the original minimal witness,
including its escaping lift and the literal Sylow subgroup T. -/
theorem local_minimal_five_single_factor_control
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ (I : Subgroup G) (X : Subgroup (HStar I)) (Y : Subgroup I),
      I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      (∀ D : Subgroup G, D ∈ F.Hz L (normalizer (L : Set G)) → D < I →
        pCore 5 (HStar D) = ⊥) ∧
      X = pCore 5 (HStar I) ∧ (Nat.card X = 5 ∨ Nat.card X = 25) ∧
      Y.Normal ∧ IsPPerfect 2 Y ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* X) ∧
      ¬ Y.map I.subtype ≤ normalizer (L : Set G) ∧
      I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∧
      Group.IsSolvable I ∧ ((F.Li L 1).subgroupOf I).Normal ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          let := BinaryGroupAction.action a.representation
          ∃ f : CanonicalFiveDihedralFamily (G := HStar I)
              (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))),
            X ≤ f.product ∧
            (Nat.card (smallSupportFactors (HStar I)
              (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 1 ∨
             Nat.card (smallSupportFactors (HStar I)
              (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 2) ∧
            (Nat.card (smallSupportFactors (HStar I)
                (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 1 →
              omegaOneAmbient (T : Subgroup G) ≤ F.Ri L 1 ∧
              omegaOneAmbient (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
              ∀ k : ℕ, k < twoRank (T : Subgroup G) →
                thompsonJ (T : Subgroup G) k =
                  thompsonJ ((L ⊔ (T : Subgroup G)).pCoreIn 2) k ∧
                L ⊔ (T : Subgroup G) ≤ normalizer (thompsonJ (T : Subgroup G) k : Set G)) := by
  obtain ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,
      hYm,hYk,he,hout,hgen,hs,hn,hpoint,hm,hU,a,A,R,hAR,hA,hfaith,hR,hRE,hRc,
      hcub,hfixed,hcomm,hmove,hcompl,hcan,hpos,hcount,hcentral,f,i,hi,hfi,hXD,hPD,hfull⟩ :=
    local_minimal_five_dihedral h hab structural previous J hJ hne
  let := hU
  let := BinaryGroupAction.action a.representation
  refine ⟨I,X,Y,hIJ,hI,hproper,hcore,hcard,hYn,hYp,hYm,hYk,he,hout,hgen,hs,hn,
    hU,a,f,hXD,by omega,?_⟩
  intro hone
  have hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I :=
    sup_le (fun _ hx => hI.1.2 (Or.inl hx)) (fun _ hx => hI.1.2 (Or.inr hx))
  have hΩ := local_single_five_omega_le_point_core h structural I hBI hn a i hone
  exact ⟨hΩ,omega_le_seed_core_of_le_point_core h structural hΩ,
    thompson_normalized_of_omega_le_point_core h structural hΩ⟩

/-- The original minimal five-core witness has exactly two canonical factors:
Thompson factorization rules out the singleton case. -/
theorem local_minimal_five_single_factor_exclusion
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ (I : Subgroup G) (X : Subgroup (HStar I)) (Y : Subgroup I),
      I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      (∀ D : Subgroup G, D ∈ F.Hz L (normalizer (L : Set G)) → D < I →
        pCore 5 (HStar D) = ⊥) ∧
      X = pCore 5 (HStar I) ∧ (Nat.card X = 5 ∨ Nat.card X = 25) ∧
      Y.Normal ∧ IsPPerfect 2 Y ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* X) ∧
      ¬ Y.map I.subtype ≤ normalizer (L : Set G) ∧
      I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∧
      Group.IsSolvable I ∧ ((F.Li L 1).subgroupOf I).Normal ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          let := BinaryGroupAction.action a.representation
          ∃ f : CanonicalFiveDihedralFamily (G := HStar I)
              (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))),
            X ≤ f.product ∧
            Nat.card (smallSupportFactors (HStar I)
              (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 2 := by
  obtain ⟨I,X,Y,hIJ,hI,hproper,hcore,hcard,hYn,hYp,hYm,hYk,he,hout,hgen,hs,hn,
      hU,a,f,hXD,hcount,hcontrol⟩ :=
    local_minimal_five_single_factor_control h hab structural previous J hJ hne
  let := hs
  let := hYn
  let := hU
  let := BinaryGroupAction.action a.representation
  have hX5 : IsPGroup 5 X := by rw [hcore]; exact pCore_isPGroup
  have hY5 : IsPGroup 5 (Y ⧸ pCore 2 Y) := hX5.of_equiv he.some.symm
  have htwo : Nat.card (smallSupportFactors (HStar I)
      (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 2 := by
    rcases hcount with hone | htwo
    · exact False.elim ((local_five_lift_not_omega_le_point_core h structural I hI Y hY5 hout)
        (hcontrol hone).1)
    · exact htwo
  exact ⟨I,X,Y,hIJ,hI,hproper,hcore,hcard,hYn,hYp,hYm,hYk,he,hout,hgen,hs,hn,
    hU,a,f,hXD,htwo⟩

section FixedWitness
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

/-- The singleton case is impossible on any fixed minimal witness and its
original quotient action; minimality identifies the point-normal lift with I. -/
theorem local_minimal_five_single_factor_impossible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar I) ≠ ⊥)
    (hmin : ∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
      pCore 5 (HStar E) = ⊥)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    let := BinaryGroupAction.action a.representation
    ∀ (_i : smallSupportFactors (HStar I)
        (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
      Nat.card (smallSupportFactors (HStar I)
        (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) ≠ 1 := by
  intro _ i hone
  obtain ⟨I',X,Y,hI'I,hI',_,hcore,hcard,hYn,_,_,_,he,hout,_,hs,hn,_⟩ :=
    local_minimal_five_single_factor_control h hab structural previous I hI hne
  have hXne : X ≠ ⊥ := by
    intro hz
    rcases hcard with hc | hc <;> rw [hz,card_bot] at hc <;> omega
  have heq : I' = I := by
    by_contra hne'
    exact hXne (hcore.trans (hmin I' hI' (lt_of_le_of_ne hI'I hne')))
  subst I'
  let := hs
  let := hYn
  have hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I :=
    sup_le (fun _ hx => hI.1.2 (Or.inl hx)) (fun _ hx => hI.1.2 (Or.inr hx))
  have hX5 : IsPGroup 5 X := by rw [hcore]; exact pCore_isPGroup
  have hY5 : IsPGroup 5 (Y ⧸ pCore 2 Y) := hX5.of_equiv he.some.symm
  exact (local_five_lift_not_omega_le_point_core h structural I hI Y hY5 hout)
    (local_single_five_omega_le_point_core h structural I hBI hn a i hone)

/-- The actual local five-rank bounds the canonical factors of every faithful
literal quotient action, with no choice of a replacement action. -/
theorem local_five_factor_count_le_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    let := BinaryGroupAction.action a.representation
    Nat.card (smallSupportFactors (HStar I)
      (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) ≤ 2 := by
  intro _
  let W := Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I))
  let := BinaryGroupAction.action a.representation
  let : IsElementaryAbelian 2 (Multiplicative W) := BinaryGroupAction.elementary
  let : FaithfulSMul (HStar I) (Multiplicative W) :=
    BinaryGroupAction.faithful a.representation a.faithful
  let C := smallSupportFactors (HStar I) (Multiplicative W) 2
  let : Fintype C := Fintype.ofFinite C
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro hz
    have hc := F.card 1 (by decide)
    rw [hz,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  have hrI : primeRank 5 I ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 5 (inclusion hI.2.1) (inclusion_injective hI.2.1)).trans
      ((h.source.simpleQTKE.twoLocal_sqtk hH).stronglyQuasithin 5 Nat.prime_five (by decide))
  have hrX : primeRank 5 (pCore 5 (HStar I)) ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 5 _ (pCore 5 (HStar I)).subtype_injective).trans
      ((primeRank_quotient_le_of_isTwoGroup 5 (by decide) (pCore 2 I) pCore_isPGroup).trans hrI)
  change Nat.card C ≤ 2
  rw [Nat.card_eq_fintype_card]
  exact (Chapter13.Section08.SolvableExclusion.Five.canonicalFive_count_le_subgroup_rank
    (fun N : C => N.val) (fun N => N.property) Subtype.val_injective (pCore 5 (HStar I))
    (fun N => IsPGroup.le_pCore_of_le_fitting
      (IsPGroup.of_card (n := 1) (by simpa using N.property.2.1)) N.property.1)).trans hrX

end FixedWitness

/-- On the same original endpoint and common eight-group, exactly two
canonical factors remain and both endpoint two-cores centralize that group.
The simultaneous-cubic alternative is retained, not asserted impossible. -/
theorem local_minimal_five_simultaneous_cubic
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ I : Subgroup G, I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      pCore 5 (HStar I) ≠ ⊥ ∧
      (∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
        pCore 5 (HStar E) = ⊥) ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          let : IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
          ∃ hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis,
            ∃ c : SelectedQuadraticEndpoint hf a,
              c.endpoint.representative ∉ F.H ∧
              let A := actorImage I (c.endpoint.conjugate (F.UH I))
              let C := ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆
              let := BinaryGroupAction.action a.representation
              ∃ (f : CanonicalFiveDihedralFamily (G := HStar I)
                  (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))))
                (i : smallSupportFactors (HStar I)
                  (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
                A ≤ f.factor i ∧ Nat.card A = 2 ∧
                C = Chapter14.Section06.OddNormalizer.supportPreimage a
                  (subspaceCommutator a.representation ⊤ A) ∧
                IsElementaryAbelian 2 C ∧ Nat.card C = 8 ∧
                F.Vi 1 ≤ C ∧ c.endpoint.conjugate (F.Vi 1) ≤ C ∧
                F.Vi 1 ≠ c.endpoint.conjugate (F.Vi 1) ∧
                Nat.card (smallSupportFactors (HStar I)
                  (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 2 ∧
                I.pCoreIn 2 ≤ centralizer (C : Set G) ∧
                (c.endpoint.conjugate I).pCoreIn 2 ≤ centralizer (C : Set G) := by
  obtain ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,hout,f,i,hAi,hAc,hpre,hCE,hCc,hbase,hopp,hnep,halt⟩ :=
    local_minimal_five_two_factor_exclusion h hab structural previous faithful J hJ hne
  let := hU
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  let := BinaryGroupAction.action a.representation
  have hbound := local_five_factor_count_le_two h I hI a
  have hnotone := local_minimal_five_single_factor_impossible h hab structural previous
    I hI hneI hmin a i
  let : Nonempty (smallSupportFactors (HStar I)
      (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) := ⟨i⟩
  have hpos : 0 < Nat.card (smallSupportFactors (HStar I)
      (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) := Nat.card_pos
  have htwo : Nat.card (smallSupportFactors (HStar I)
      (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 2 := by omega
  exact ⟨I,hIJ,hI,hneI,hmin,hU,a,hf,c,hout,f,i,hAi,hAc,hpre,hCE,hCc,hbase,hopp,hnep,
    htwo,halt.resolve_right (fun hn => hn htwo)⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
