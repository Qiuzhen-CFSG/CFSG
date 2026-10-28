module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.MovingRank
public import CFSG.Quasithin.ChapterA.Section02.OddModelTwoRank
public import Theory.Alternating.PrimeRank
public import Theory.SpecificGroups.PSL5Two.TwoRankUpper

/-!
# First source catalogue exclusions for nonsingular ordinary components

The actual moving subgroup injects into K/Z(K), giving two-rank at least
six in degree four and eight in degree five. This excludes every odd-field
row and every alternating row in Theorem C, including L₄(2). In degree
five it also excludes L₅(2). Theorem A transports SQTK to the literal simple
central quotient, and Theorem C supplies its remaining actual models.

The final chosen-module application constructs the compatible model and
adapted conjugate. The remaining Bender, even-rank-two, sporadic and
degree-four L₅(2) rows, together with the later normal and parabolic branches,
remain owned by qt-d-double-natural-centralizers. This is not a proof of 12.1.1.
Source: Aschbacher--Smith, 12.1.1 and A.2.3, printed pp.788 and32--33.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The inherited SQTK hypothesis gives the genuine catalogue for K/Z(K). -/
theorem doubleNatural_nonsingular_component_centralQuotient_catalogue
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ w : componentOrbit V (T : Subgroup G), B.quadratic (Additive.ofMul w) = 1 →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ChapterA.Section02.IsTheoremCModel (K ⧸ center K) := by
  let := D.doubledOrbit_elementary h
  intro w hw K hK
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hK.1) (hG := hK.2.2)
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  have hA := h.simpleQTKE.twoLocal_sqtk
    (isTwoLocal_involution_centralizer (D.doubleNatural_point_orderOf_two h B w hw))
  let j := inclusion hK.1
  have hs : IsSQTK KnownSimple.IsKnownSimple K :=
    ⟨hA.stronglyQuasithin.of_injective j (inclusion_injective _),
      hA.isKGroup.of_injective j (inclusion_injective _)⟩
  have hsem : componentLayer K = ⊤ := by
    apply top_unique
    exact le_sSup ⟨(inferInstance : (⊤ : Subgroup K).Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (topEquiv (G := K)).symm⟩
  have hsemi : ChapterA.Section02.IsSemisimple (K ⧸ center K) :=
    componentLayer_eq_top_of_surjective (QuotientGroup.mk' (center K))
      (QuotientGroup.mk'_surjective _) hsem
  have hsec : ChapterA.Section02.IsSectionOf (K ⧸ center K) K :=
    ChapterA.Section02.IsSectionOf.of_surjective _ (QuotientGroup.mk'_surjective (center K))
  have hq := ChapterA.Section02.theoremA_knownSimple.stronglyQuasithin_section
    hs.stronglyQuasithin hs.isKGroup hsec hsemi
  exact ChapterA.Section02.theoremC_knownSimple inferInstance
    (Group.IsPerfect.not_isMulCommutative _) hq (hs.isKGroup.quotient _)

/-- The ordinary component central quotient cannot be an odd-field row. -/
theorem doubleNatural_adapted_component_not_odd
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ¬ ChapterA.Section02.IsTheoremCOddModel (K ⧸ center K) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK hm
  have hr := D.doubleNatural_adapted_component_centralQuotient_rank h B S w hw K hK
  have hu := hm.twoRank_le_two
  have hn := B.degree
  omega

/-- Every alternating row of Theorem C has insufficient two-rank. -/
theorem doubleNatural_adapted_component_not_alternating
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ∀ m : ℕ, m ≤ 8 → ¬ Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin m)) := by
  let := D.doubledOrbit_elementary h
  rintro S w hw K hK m hm ⟨e⟩
  have hr := D.doubleNatural_adapted_component_centralQuotient_rank h B S w hw K hK
  rw [primeRank_equiv 2 e,
    (GLS3.Chapter5.PRank.alternating_hasPRank_two m).primeRank_eq Nat.prime_two] at hr
  have hn := B.degree
  omega

/-- The degree-five moving subgroup also exceeds the two-rank of L₅(2). -/
theorem doubleNatural_five_adapted_component_not_linearFive
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ¬ ClassicalGroup.IsPSL (K ⧸ center K) 5 2 := by
  let := D.doubledOrbit_elementary h
  rintro S w hw K hK ⟨F,_,_,hF,⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  have hr := D.doubleNatural_adapted_component_centralQuotient_rank h B S w hw K hK
  rw [primeRank_equiv 2 (e.trans (Atlas.fieldEquivPSL 5 eF))] at hr
  have hu := Theory.SpecificGroups.PSL5Two.primeRank_le_six
  omega

/-- The remaining rows retain their actual central-quotient models and the original degree. -/
theorem doubleNatural_adapted_component_remaining_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ClassificationModels.IsBenderModel (K ⧸ center K) ∨
        (∃ f, ChapterA.Section02.IsTheoremCRankTwoModel (K ⧸ center K) f) ∨
        (n = 4 ∧ ClassicalGroup.IsPSL (K ⧸ center K) 5 2) ∨
        ChapterA.Section02.IsTheoremCSporadicModel (K ⧸ center K) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK
  cases D.doubleNatural_nonsingular_component_centralQuotient_catalogue h B w hw.nonsingular K hK with
  | alternating m hm he =>
    exact (D.doubleNatural_adapted_component_not_alternating h B S w hw K hK m hm he).elim
  | odd hm => exact (D.doubleNatural_adapted_component_not_odd h B S w hw K hK hm).elim
  | bender hm => exact .inl hm
  | rank_two f hm => exact .inr (.inl ⟨f,hm⟩)
  | linear_binary m hm he =>
    rcases hm with rfl | rfl
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
      let : Fintype F := Fintype.ofFinite F
      let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
        simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
      exact (D.doubleNatural_adapted_component_not_alternating h B S w hw K hK 8 (by decide)
        ⟨(e.trans (Atlas.fieldEquivPSL 4 eF)).trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8⟩).elim
    · rcases B.degree with hn | hn
      · exact .inr (.inr (.inl ⟨hn,he⟩))
      · subst n
        exact (D.doubleNatural_five_adapted_component_not_linearFive h B S w hw K hK he).elim
  | sporadic hm => exact .inr (.inr (.inr hm))

/-- The original nonsingular point has an adapted conjugate with characteristic two or a normal component in the reduced catalogue. -/
theorem doubleNatural_nonsingular_characteristic_or_models_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ w : componentOrbit V (T : Subgroup G), B.quadratic (Additive.ofMul w) = 1 →
      ∃ l : L, ∃ w' : componentOrbit V (T : Subgroup G),
        (w' : G) = (l : G) * (w : G) * (l : G)⁻¹ ∧ B.quadratic (Additive.ofMul w') = 1 ∧
        (generalizedFitting (B.pointCentralizer w') = pCore 2 (B.pointCentralizer w') ∨
        ∃ K : Subgroup G, IsComponentIn K (B.pointCentralizer w') ∧
          (K.subgroupOf (B.pointCentralizer w')).Normal ∧ B.pointResidual w' ≤ K ∧
          2 * (n - 1) ≤ primeRank 2 (K ⧸ center K) ∧
          (ClassificationModels.IsBenderModel (K ⧸ center K) ∨
          (∃ f, ChapterA.Section02.IsTheoremCRankTwoModel (K ⧸ center K) f) ∨
          (n = 4 ∧ ClassicalGroup.IsPSL (K ⧸ center K) 5 2) ∨
          ChapterA.Section02.IsTheoremCSporadicModel (K ⧸ center K))) := by
  let := D.doubledOrbit_elementary h
  intro w hw
  obtain ⟨S⟩ := B.nonempty_sourceModel
  obtain ⟨l,w',he,hw'⟩ := D.doubleNatural_adaptedPoint h B S w hw
  refine ⟨l,w',he,hw'.nonsingular,?_⟩
  rcases D.doubleNatural_adapted_characteristic_or_normal_component h B S w' hw' with
    hc | ⟨K,hK,hn,hRK,_⟩
  · exact .inl hc
  · exact .inr ⟨K,hK,hn,hRK,
      D.doubleNatural_adapted_component_centralQuotient_rank h B S w' hw' K hK,
      D.doubleNatural_adapted_component_remaining_models h B S w' hw' K hK⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
