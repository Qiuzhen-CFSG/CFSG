module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Linear
public import Theory.SpecificGroups.PSL2.ThompsonBorel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.HigherField.Complete

/-!
# Excluding ordinary PSL₂ components above the field of four elements

The model Thompson theorem treats both component-normalizing and exchanging
Sylow actions. Together with two-perfectness and the relative centralizer
comparison, original Thompson control excludes the full Borel row for every
field degree greater than two. The remaining rank-one alternatives are the
literal L₂(4) Borel row and the unitary row.
Source: Aschbacher--Smith 15.1.21(i), printed pp.1097--1098.
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
variable {F : Type} [Field F] [Finite F] {n : ℕ}

/-- Degree greater than two supplies the required normalization of the original J(S). -/
theorem PreExclusionSource.rankOne_linear_borel_thompson_gt_two
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hn : 2 < n) (hF : Nat.card F=2^n) (e : d.L ≃* PSL(2,F)) :
    d.ordinaryBorel ≤ normalizer (elementaryAbelianMaxJ d.S : Set G) := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨P,hP⟩ := s.component_sylow
  have hP' : (P : Subgroup d.L)=d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
  have hj := Theory.PSL2.OrdinaryBorel.component_normalizer_thompson_field
    d.G1 d.L d.S d.L_component.1 d.S_le_G1 hL (T.isPGroup'.to_le d.S_le_T)
    (s.ordinary_normalizer_relIndex_le_two (h := h) hG hL) P (hP ▸ d.SL_le_S) hn hF e
  change (normalizer ((P : Subgroup d.L) : Set d.L)).map d.L.subtype ≤ _ at hj
  rw [hP'] at hj
  exact hj

/-- The full linear constructor of degree greater than two is impossible, with its literal Borel clause. -/
theorem PreExclusionSource.false_of_rankOne_linear_gt_two
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hn : 2 < n) (hm : ClassicalGroup.IsPSL d.L 2 (2^n))
    (hB : d.ML=d.ordinaryBorel) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  exact s.no_thompson_borel (h := h) hG hM hJ
    (s.rankOne_linear_borel_twoPerfect (h := h) (by omega) hF e) (hB ▸ d.ML_le_MZ)
    (s.rankOne_linear_borel_thompson_gt_two (h := h) hG hL hn hF e)
    (s.rankOne_linear_borel_centralizers (h := h) hL (by omega) hF e)

/-- The literal rank-one row reduces to L₂(4) or a unitary model. -/
theorem PreExclusionSource.rankOne_after_linear_gt_two
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hmodel : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))
    (hB : d.ML=d.ordinaryBorel) :
    ClassicalGroup.IsPSL d.L 2 4 ∨
      (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSU d.L 3 (2^f)) := by
  rcases s.rankOne_after_all_suzuki (h := h) hG hM hJ hu hL hmodel hB with ⟨f,hf,hm⟩ | hm
  · by_cases he : f=2
    · exact Or.inl (by simpa [he] using hm)
    · exact (s.false_of_rankOne_linear_gt_two (h := h) hG hM hJ hL (by omega) hm hB).elim
  · exact Or.inr hm

/-- Constructor-aware early quotient reduction. Only the L₂(4) and unitary
row exclusions remain with this task; the initial catalogue remains explicit. -/
theorem Ordinary20Alternatives.postRankOneModel_of_four_unitary_exclusions
    (ha : d.Ordinary20Alternatives) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hfour : ClassicalGroup.IsPSL d.L 2 4 → d.ML=d.ordinaryBorel → False)
    (hunitary : (∃ f : ℕ, 2≤f ∧ ClassicalGroup.IsPSU d.L 3 (2^f)) →
      d.ML=d.ordinaryBorel → False) : OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  apply ha.postRankOneModel_of_rankOne_exclusion (h := h) s hG hM hJ hu hL
  intro hm hB
  rcases s.rankOne_after_linear_gt_two (h := h) hG hM hJ hu hL hm hB with hm | hm
  · exact hfour hm hB
  · exact hunitary hm hB

/-- The early exchanged-source application retains the very same pre-exclusion
witness. The initial catalogue and the two remaining model rows are explicit
premises; this is not the completed source 15.1.21 assembly. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_four_unitary_rows
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcatalogue : IsComponent d.G1 (d.L.subgroupOf d.G1) → d.Ordinary20Alternatives)
    (hfour : IsComponent d.G1 (d.L.subgroupOf d.G1) →
      ClassicalGroup.IsPSL d.L 2 4 → d.ML=d.ordinaryBorel → False)
    (hunitary : IsComponent d.G1 (d.L.subgroupOf d.G1) →
      (∃ f : ℕ, 2≤f ∧ ClassicalGroup.IsPSU d.L 3 (2^f)) → d.ML=d.ordinaryBorel → False) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) :=
  e.not_ordinary_of_post_rank_one_catalogue hG hM hu h (fun hL =>
    (hcatalogue hL).postRankOneModel_of_four_unitary_exclusions (h := h) s hG hM hJ hu hL
      (hfour hL) (hunitary hL))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
