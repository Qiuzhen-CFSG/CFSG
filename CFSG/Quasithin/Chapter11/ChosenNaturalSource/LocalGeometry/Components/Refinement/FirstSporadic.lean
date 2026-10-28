module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstCubic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.OddExtensions
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.FourSporadic
public import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.Mathieu.M22.TripleCover.ScalarAutomorphisms
public import Theory.Mathieu.M23.Properties.OuterRestriction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.BlockGeometry
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.Structure
public import Theory.SpecificGroups.Janko4.Model.Center
public import Theory.SpecificGroups.Rudvalis.ComponentFacts
public import Theory.SpecificGroups.Rudvalis.Model.Certification
public import Theory.SpecificGroups.Rudvalis.Model.Order

/-!
# Cubic exclusion of the six centerless sporadic rows

For M₂₂, M₂₃, J₂, J₄, HS and Ru, the concrete model supplies a trivial
center, cubic rank at least two and a two-group outer automorphism group.
The first-normalizer cubic argument then contradicts the faithful Cartan
factor outside its containing C-component. The combined field-four sieve
also applies the alternating-cover exclusions and the two proved odd-kernel
extension refinements, retaining every row that still requires proof.

All model comparisons refer to the intrinsic K/O₂(K). The original flag,
L₁, K and Cartan factor are preserved in the consumer. The relative-components
owner retains the unresolved rows, triangle and source-family assembly;
the preceding flag/Cartan inputs remain with their existing producer and
parent qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.1(3) and the first-index proof of 11.1.2, printed pp.761--762.
The imported concrete models retain their ATLAS source attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open Chapter1.Section02.LocalModels

/-- The six centerless sporadic rows of the field-four list. This is a model
predicate for a proved exclusion, not an exhaustive source classification. -/
def FirstCubicSporadic (A : Type*) [Group A] : Prop :=
  Nonempty (A ≃* Sporadic.Mathieu.M22) ∨
  Nonempty (A ≃* Sporadic.Mathieu.M23) ∨
  Nonempty (A ≃* Sporadic.LeechRelated.J2.Carrier) ∨
  Nonempty (A ≃* Janko4.Model) ∨
  Nonempty (A ≃* Sporadic.LeechRelated.HS.Carrier) ∨
  Nonempty (A ≃* Rudvalis.Model)

/-- Public constructor for the three centerless small sporadic carriers.
Consumers need not unfold the internal six-carrier predicate. -/
theorem FirstCubicSporadic.of_small_carrier {A : Type*} [Group A]
    (h : Nonempty (A ≃* Sporadic.Mathieu.M22) ∨
      Nonempty (A ≃* Sporadic.Mathieu.M23) ∨
      Nonempty (A ≃* Sporadic.LeechRelated.HS.Carrier)) : FirstCubicSporadic A := by
  rcases h with h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inr (.inr (.inl h))))

private theorem transport_cubic_data
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (hz : center B = ⊥) (hr : 2 ≤ primeRank 3 B)
    (ho : IsPGroup 2 (MulAut.Outer B)) :
    center A = ⊥ ∧ 2 ≤ primeRank 3 A ∧ IsPGroup 2 (MulAut.Outer A) := by
  refine ⟨?_,?_,ho.of_equiv (MulAut.outerCongr e).symm⟩
  · apply eq_bot_iff.mpr
    intro z hzA
    exact e.map_eq_one_iff.mp (hz.le ((centerCongr e) ⟨z,hzA⟩).property)
  · rwa [primeRank_congr 3 e]

private theorem sporadic_cubic_data
    {A : Type*} [Group A] [Finite A] (hm : FirstCubicSporadic A) :
    center A = ⊥ ∧ 2 ≤ primeRank 3 A ∧ IsPGroup 2 (MulAut.Outer A) := by
  open ChapterA.Section03.OddPrime.SourceModels.FourSporadic in
  rcases hm with e | e | e | e | e | e
  · exact transport_cubic_data e.some Sporadic.Mathieu.m22_center_eq_bot
      Sporadic.Mathieu.m22_primeRank_three.ge
      (IsPGroup.of_card_dvd_pow (n := 1)
        Sporadic.Mathieu.M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two)
  · have hr : 2 ≤ primeRank 3 Sporadic.Mathieu.M23 := by
      exact Sporadic.Mathieu.m22_primeRank_three.ge.trans
        ((primeRank_equiv 3 Sporadic.Mathieu.m23EquivM22PointStabilizer).le.trans
          (primeRank_subgroup_le 3 _))
    exact transport_cubic_data e.some Sporadic.Mathieu.M23Geometry.m23_center_eq_bot hr
      Sporadic.Mathieu.m23_outer_isTwoGroup
  · exact transport_cubic_data e.some
      Sporadic.LeechRelated.J2.ExceptionalParabolics.BlockGeometry.center_eq_bot
      Sporadic.LeechRelated.J2.three_rank_ge_two Sporadic.LeechRelated.J2.outer_isTwoGroup
  · exact transport_cubic_data e.some Janko4.model_center_eq_bot
      j4_three_rank_ge_two Janko4.AdequateLocal.outer_isPGroup_two
  · exact transport_cubic_data e.some Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot
      Sporadic.LeechRelated.HS.ThreeRank.two_le_primeRank
      (Sporadic.LeechRelated.HS.outer_isPGroup_two_of_pointStabilizer_map
        Sporadic.LeechRelated.HS.pointStabilizer_map Sporadic.LeechRelated.HS.normalizer_relIndex_dvd_two_pow)
  · let : MulAction.IsPreprimitive Rudvalis.Model (Fin 4060) := Rudvalis.model_isPreprimitive
    let : IsSimpleGroup Rudvalis.Model := Rudvalis.simple_of_card_of_primitive Rudvalis.model_card
    exact transport_cubic_data e.some Rudvalis.LowCentralizers.model_center_eq_bot
      Rudvalis.three_rank_ge_two Rudvalis.outer_isPGroup_two

variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- All six centerless sporadic rows in 11.1.1(3) are excluded at the first
normalizer, with their concrete centers, ranks and outer groups discharged. -/
theorem first_component_not_cubic_sporadic
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G)) (hXcard : Nat.card X₁ = 3)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥) :
    ¬ FirstCubicSporadic (K ⧸ pCore 2 K) := by
  intro hs
  obtain ⟨hz,hr,ho⟩ := sporadic_cubic_data hs
  exact first_component_not_centerless_cubic D S f hm hfix hK hLK hXN hXcard hfaith hz hr ho

/-- The field-four first-normalizer list after the proved cubic exclusions
and odd-extension refinement. The five remaining model rows are retained
explicitly; no remaining local exclusion or triangle is assumed proved. -/
theorem first_fieldFour_cubic_sieve
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G)) (hXcard : Nat.card X₁ = 3)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hfour : S.field.degree = 2) (hk : FieldFourOvergroup (K ⧸ pCore 2 K)) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree ∨
      (∃ p, Source.ExceptionalPrime p ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25 ∨
      (∃ u, IsPSLSign (K ⧸ pCore 2 K) u 3 5 ∨ IsSLSign (K ⧸ pCore 2 K) u 3 5) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) ∨ IsM22Cover (K ⧸ pCore 2 K) := by
  have hseven := first_component_not_seven D S f hm hfix hK hLK hXN hXcard hfaith
  have hspor := first_component_not_cubic_sporadic D S f hm hfix hK hLK hXN hXcard hfaith
  cases hk with
  | alternating h => exact (hseven (.inl h)).elim
  | alternatingCover h => exact (hseven (.inr h)).elim
  | primeLinear p hp h => exact .inr (.inl ⟨p,hp,h⟩)
  | linearTwentyFive h => exact .inr (.inr (.inl h))
  | three u h => exact .inr (.inr (.inr (.inl ⟨u,h⟩)))
  | m22 h => exact (hspor (.inl h)).elim
  | m22Cover h => exact .inr (.inr (.inr (.inr (.inr h))))
  | m23 h => exact (hspor (.inr (.inl h))).elim
  | j1 h => exact .inr (.inr (.inr (.inr (.inl h))))
  | j2 h => exact (hspor (.inr (.inr (.inl h)))).elim
  | j4 h => exact (hspor (.inr (.inr (.inr (.inl h))))).elim
  | hs h => exact (hspor (.inr (.inr (.inr (.inr (.inl h)))))).elim
  | ru h => exact (hspor (.inr (.inr (.inr (.inr (.inr h)))))).elim
  | nilpotentExtension h => exact .inl (first_refinement_of_nilpotent_extension hfour h)
  | elementaryExtension p hp h => exact .inl (first_refinement_of_elementary_extension hfour hp h)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
