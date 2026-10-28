module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.LinearHigherDegree
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.PrimeActor
public import Theory.SpecificGroups.PSL2.ThompsonSylow
public import Theory.SpecificGroups.PSL2.FourThompsonActor

/-!
# The exceptional ordinary L₂(4) row and complete linear elimination

Paired-component replacement puts J(S) in the normalizer of L and puts
S_L in J(S). The actual L₂(4) automorphism calculation then gives either
Borel normalization of J(S), or centralization by every odd-prime subgroup
normalizing L and J(S). The first alternative contradicts the existing
residual control. In the second, the original Thompson control identifies
J(S) with J(T), and the already constructed p-subgroup Y centralizes L,
contradicting its moving commutator.

Thus every ordinary linear constructor is excluded. The constructor-aware
quotient and same-component adapters retain only the unitary row exclusion
and the initial ordinary catalogue as explicit premises. Their final discharge
remains with qt-e-15121-ordinary-rankone and the initial catalogue owner
qt-e-15122-ordinary-pre-exclusion; no full catalogue theorem is asserted here.
Source: Aschbacher--Smith 15.1.21(ii), printed p.1098.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The exceptional linear row is excluded by the actual original prime actor. -/
theorem PreExclusionSource.false_of_rankOne_linear_four
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p=3 ∨ p=5)
    (hm : ClassicalGroup.IsPSL d.L 2 4) (hB : d.ML=d.ordinaryBorel) : False := by
  let := h.elementary
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (f:=2) hF
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (Theory.PSL2.BinaryField 2) := Fintype.ofFinite _
  let eF : F ≃+* Theory.PSL2.BinaryField 2 := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card,Fintype.card_eq_nat_card,hF,
      GaloisField.card 2 2 (by decide)]
    decide)
  let e4 := e.trans (Atlas.fieldEquivPSL 2 eF)
  obtain ⟨P,hP⟩ := s.component_sylow
  have hPS : (P : Subgroup d.L).map d.L.subtype ≤ d.S := hP ▸ d.SL_le_S
  have hi := s.ordinary_normalizer_relIndex_le_two (h := h) hG hL
  have hJN := Theory.PSL2.OrdinaryBorel.component_thompson_normalizes
    d.G1 d.L d.S d.L_component.1 d.S_le_G1 hL hi P hPS (by decide : 2≤2) e4
  have hPJ := Theory.PSL2.OrdinaryBorel.component_thompson_contains_sylow
    d.G1 d.L d.S d.L_component.1 d.S_le_G1 hL hi P hPS (by decide : 2≤2) e4
  have hJS : elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ (T : Subgroup G) :=
    (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).1
  have hJtwo : IsPGroup 2 (elementaryAbelianMaxJ d.S) :=
    (T.isPGroup'.to_le d.S_le_T).to_le (sSup_le fun _ hA => hA.1)
  rcases Theory.PSL2.OrdinaryBorel.four_borel_or_odd_actor_centralizes
    d.L (elementaryAbelianMaxJ d.S) hJtwo hJN P hPJ e4 with hBN | hcent
  · have hP' : (P : Subgroup d.L)=d.SL.subgroupOf d.L := by
      apply map_injective d.L.subtype_injective
      rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
    change (normalizer ((P : Subgroup d.L) : Set d.L)).map d.L.subtype ≤ _ at hBN
    rw [hP'] at hBN
    exact s.no_thompson_borel (h := h) hG hM hJ
      (s.rankOne_linear_borel_twoPerfect (h := h) (by decide : 2≤2) hF e)
      (hB ▸ d.ML_le_MZ) hBN
      (s.rankOne_linear_borel_centralizers (h := h) hL (by decide : 2≤2) hF e)
  · obtain ⟨Y,hY,hYN,hncent⟩ := s.rankOne_prime_actor_noncentral (h := h) hG hM hJ
    apply hncent
    apply hcent p (by rcases hp with rfl | rfl <;> decide) Y hY.prime_group hYN
    rw [hJS]
    exact hY.normalizer_le.trans inf_le_right

/-- All linear and Suzuki constructors are excluded; only the literal unitary row remains. -/
theorem PreExclusionSource.rankOne_after_all_linear
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p=3 ∨ p=5)
    (hmodel : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))
    (hB : d.ML=d.ordinaryBorel) :
    ∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSU d.L 3 (2^f) := by
  rcases s.rankOne_after_linear_gt_two (h := h) hG hM hJ hu hL hmodel hB with hm | hm
  · exact (s.false_of_rankOne_linear_four (h := h) hG hM hJ hL hp hm hB).elim
  · exact hm

/-- Early quotient reduction after all linear rows, retaining the initial
catalogue and the pending unitary row exclusion. -/
theorem Ordinary20Alternatives.postRankOneModel_of_unitary_exclusion
    (ha : d.Ordinary20Alternatives) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p=3 ∨ p=5)
    (hunitary : (∃ f : ℕ, 2≤f ∧ ClassicalGroup.IsPSU d.L 3 (2^f)) →
      d.ML=d.ordinaryBorel → False) : OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  exact ha.postRankOneModel_of_four_unitary_exclusions (h := h) s hG hM hJ hu hL
    (s.false_of_rankOne_linear_four (h := h) hG hM hJ hL hp) hunitary

/-- Same-component application after all linear rows. The remaining premises
are discharged by this task's unitary proof and the initial catalogue owner. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_unitary_row
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hp : p=3 ∨ p=5)
    (hcatalogue : IsComponent d.G1 (d.L.subgroupOf d.G1) → d.Ordinary20Alternatives)
    (hunitary : IsComponent d.G1 (d.L.subgroupOf d.G1) →
      (∃ f : ℕ, 2≤f ∧ ClassicalGroup.IsPSU d.L 3 (2^f)) → d.ML=d.ordinaryBorel → False) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) :=
  e.not_ordinary_of_post_rank_one_catalogue hG hM hu h (fun hL =>
    (hcatalogue hL).postRankOneModel_of_unitary_exclusion (h := h) s hG hM hJ hu hL hp
      (hunitary hL))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
