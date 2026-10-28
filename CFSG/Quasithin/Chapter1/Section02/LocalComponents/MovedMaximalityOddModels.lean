module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalitySmallModels
public import Theory.GroupTheory.CComponent.TwoRankObstruction
public import Theory.SpecificGroups.OddThreeSectionRank

/-!
# Unique components in A₇ and odd ternary Sylow overgroups

Two distinct C-components force two-rank at least four in the solvable
radical quotient. For A₇, their orders would make sixteen divide 2520.
For PSL₃(p) and PSU₃(p), the actual odd-field matrix groups have two-rank
at most three in every subgroup quotient, by their GL₂ Sylow geometry.
Thus every full-Sylow overgroup has at most one C-component in these models.

The final applications use exactly C = K.subgroupOf (K ⊔ T) and
Q = C / solvableRadical C from the moved normalized-overcomponent
obstruction. They eliminate both assigned model rows there without an
embedding-classification or normalizer hypothesis beyond the original setup.

Source: Aschbacher--Smith A.3.12, printed pp.47--48; A.3.21(a), p.55;
and the no-two-components argument in 1.2.8(1), p.506.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
open Theory.SpecificGroups.OddThreeSectionRank
variable {G : Type*} [Group G] [Finite G]

/-- The A₇ row has unique components in every full-Sylow overgroup. -/
theorem alternating_seven_sylow_overgroup_component_unique
    (hm : LocalModels.IsAlternating G 7) : SylowOvergroupComponentUnique G := by
  apply SylowOvergroupComponentUnique.of_not_sixteen_dvd_card
  obtain ⟨e⟩ := hm
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

/-- Both signs of the actual odd ternary family have the required uniqueness. -/
theorem odd_ternary_sylow_overgroup_component_unique
    {p : ℕ} (_hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hm : LocalModels.IsPSLSign G unitary 3 p) : SylowOvergroupComponentUnique G := by
  cases unitary with
  | false =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    apply SylowOvergroupComponentUnique.of_equiv e
    apply SylowOvergroupComponentUnique.of_subgroup_radicalQuotient_twoRank_le_three
    intro P
    exact psl3_subgroup_quotient_twoRank_le_three (hF.symm ▸ ho) P (solvableRadical P)
  | true =>
    obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := hm
    let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    apply SylowOvergroupComponentUnique.of_equiv e
    apply SylowOvergroupComponentUnique.of_subgroup_radicalQuotient_twoRank_le_three
    intro P
    exact psu3_subgroup_quotient_twoRank_le_three J (hF.symm ▸ ho.pow) P (solvableRadical P)

/-- A normalized overcomponent of a moved component cannot have the literal A₇ radical quotient. -/
theorem moved_normalized_not_alternating_seven
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G))
    (hmodel : let C := K.subgroupOf (K ⊔ (T : Subgroup G))
      LocalModels.IsAlternating (C ⧸ solvableRadical C) 7) : False := by
  have h := moved_normalized_remaining_simple_quotient hG T hB hK hBK hTK hm
  exact h.2.2.2 (alternating_seven_sylow_overgroup_component_unique hmodel)

/-- The same original quotient cannot be either assigned odd ternary model. -/
theorem moved_normalized_not_odd_ternary
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hmodel : let C := K.subgroupOf (K ⊔ (T : Subgroup G))
      LocalModels.IsPSLSign (C ⧸ solvableRadical C) unitary 3 p) : False := by
  have h := moved_normalized_remaining_simple_quotient hG T hB hK hBK hTK hm
  exact h.2.2.2 (odd_ternary_sylow_overgroup_component_unique hp ho unitary hmodel)

end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
