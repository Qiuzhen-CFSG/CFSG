module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.G2Geometry.Marking
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.G2Geometry.Transport
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.G2Geometry.LocalBlocks
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.G2Geometry.Normalization

/-!
# Invariant G₂ quotient parabolics for E.6.8

The two standard parabolics are marked by the actual component Sylow subgroup,
pulled back through the model map, and mapped into the specified component
quotient. They generate its component image and are invariant under N_Q(L).
When Q normalizes L, their full lifts joined with Q have characteristic two
and no relatively subnormal chi-zero blocks. The separate entry points retain
full G₂(2^f), f ≥ 2, the genuine derived G₂(2)′ carrier, and all central
two-covers of G₂(4), including trivial center.

The three geometry entry points also prove Q ≤ N_G(L), using the three-rank
argument and concrete model witnesses from `Normalization`. Thus all three
families are constructed from the E.6.1 hypotheses, with no additional
normalization or model premise. The parent OtherTypes assembly applies the
E.6.7 generation contradiction to these outputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.G2Geometry
open Chapter2.ComponentRefinement.LieType.G2

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G}

/-- Assemble both actual quotient parabolics, including their full lifted joins. -/
noncomputable def familyOfCoordinates (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G)) (d : ParabolicCoordinates L Q) :
    BlockFreeQuotientFamily Q L := by
  have hp : IsPGroup 2 Q := by
    rw [hQ]
    exact T.isPGroup'.to_le inf_le_left
  have hcore := extension_core_le_Q h hU hL hQ hN
  have hchar := characteristicTwo_pair d hN hp
  have hfree := noChiZeroBlocks_pair d hN hp
  refine {
    count := 2
    subgroup := ![quotientParabolic Q L d.first, quotientParabolic Q L d.second]
    le_component := ?_
    invariant := ?_
    characteristic_two := ?_
    no_blocks := ?_
    generate := ?_ }
  · intro i
    fin_cases i
    · exact quotientParabolic_le (show d.first ≤ L from map_subtype_le _)
    · exact quotientParabolic_le (show d.second ≤ L from map_subtype_le _)
  · intro i
    fin_cases i
    · exact quotientParabolic_invariant (show d.first ≤ L from map_subtype_le _)
        d.first_invariant
    · exact quotientParabolic_invariant (show d.second ≤ L from map_subtype_le _)
        d.second_invariant
  · intro i
    fin_cases i
    · change HasCharacteristicTwo ↥(quotientPreimage Q L (quotientParabolic Q L d.first) ⊔ Q)
      rw [quotientParabolic_lift_join (show d.first ≤ L from map_subtype_le _) hcore]
      exact hchar.1
    · change HasCharacteristicTwo ↥(quotientPreimage Q L (quotientParabolic Q L d.second) ⊔ Q)
      rw [quotientParabolic_lift_join (show d.second ≤ L from map_subtype_le _) hcore]
      exact hchar.2
  · intro i
    fin_cases i
    · change NoChiZeroBlocks (quotientPreimage Q L (quotientParabolic Q L d.first) ⊔ Q)
      rw [quotientParabolic_lift_join (show d.first ≤ L from map_subtype_le _) hcore]
      exact hfree.1
    · change NoChiZeroBlocks (quotientPreimage Q L (quotientParabolic Q L d.second) ⊔ Q)
      rw [quotientParabolic_lift_join (show d.second ≤ L from map_subtype_le _) hcore]
      exact hfree.2
  · rw [← quotientParabolic_pair_generate d]
    exact sup_le (le_iSup_of_le (0 : Fin 2) le_rfl) (le_iSup_of_le (1 : Fin 2) le_rfl)

/-- All geometric and local conditions follow from the concrete model and normalization. -/
theorem family_of_modelCase_of_normalizes (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G)) (hm : IsModelCase L) :
    Nonempty (BlockFreeQuotientFamily Q L) := by
  obtain ⟨d⟩ := exists_coordinates h hU hL hQ hm
  exact ⟨familyOfCoordinates h hU hL hQ hN d⟩

/-- The nonbinary full G₂ branch, with component normalization still explicit. -/
theorem family_of_g2_of_normalizes (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G)) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassificationModels.IsG2At L (2^f)) :
    Nonempty (BlockFreeQuotientFamily Q L) :=
  family_of_modelCase_of_normalizes h hU hL hQ hN (modelCase_of_g2 hf hm)

/-- The genuine G₂(2)′ endpoint, with component normalization still explicit. -/
theorem family_of_derived_of_normalizes (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G))
    (hm : Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    Nonempty (BlockFreeQuotientFamily Q L) :=
  family_of_modelCase_of_normalizes h hU hL hQ hN (modelCase_of_derived hm)

/-- Every central two-cover of G₂(4), with component normalization still explicit. -/
theorem family_of_cover_of_normalizes (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G))
    (hz : IsPGroup 2 (center L))
    (hm : ClassificationModels.IsG2At (L ⧸ center L) 4) :
    Nonempty (BlockFreeQuotientFamily Q L) := by
  let : IsQuasisimple L := (show IsComponentIn L (centralizer (U : Set G)) from hL).quasisimple
  exact family_of_modelCase_of_normalizes h hU hL hQ hN (modelCase_of_cover hz hm)

/-- The full G₂(2^f) branch of the invariant-parabolic argument in E.6.8.
Both ambient normalization and the family in the actual component quotient
follow from the source hypotheses and the concrete model isomorphism. -/
theorem g2_geometry (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    {f : ℕ} (hf : 2 ≤ f) (hm : ClassificationModels.IsG2At L (2^f)) :
    Q ≤ normalizer (L : Set G) ∧ Nonempty (BlockFreeQuotientFamily Q L) := by
  have hN := Normalization.component_normalizer_of_g2 h hU hL hQ hf hm
  exact ⟨hN, family_of_g2_of_normalizes h hU hL hQ hN hf hm⟩

/-- The binary endpoint of the invariant-parabolic argument in E.6.8 uses
the genuine derived G₂(2)′ carrier for normalization and both parabolics. -/
theorem derived_geometry (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hm : Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    Q ≤ normalizer (L : Set G) ∧ Nonempty (BlockFreeQuotientFamily Q L) := by
  have hN := Normalization.component_normalizer_of_derived h hU hL hQ hm
  exact ⟨hN, family_of_derived_of_normalizes h hU hL hQ hN hm⟩

/-- Every central two-cover of G₂(4) supplies the E.6.8 quotient family and
ambient normalization. The entire center is retained, including when trivial. -/
theorem cover_geometry (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hz : IsPGroup 2 (center L))
    (hm : ClassificationModels.IsG2At (L ⧸ center L) 4) :
    Q ≤ normalizer (L : Set G) ∧ Nonempty (BlockFreeQuotientFamily Q L) := by
  have hN := Normalization.component_normalizer_of_cover h hU hL hQ hz hm
  exact ⟨hN, family_of_cover_of_normalizes h hU hL hQ hN hz hm⟩

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.G2Geometry
