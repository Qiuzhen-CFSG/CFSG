module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.SecondLie
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.SourceCatalogue
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.RankOneAndExtensions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.JankoTwo
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.OddTernary
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.SecondLargeSporadic

/-!
# The remaining second-normalizer models from the source catalogue

Apply the proved 11.1.1 catalogue to the actual component containing L₂.
The full-plane degree argument excludes every non-linear Lie row. The
previous rank-one, odd ternary, sporadic and elementary-extension exclusions
remove the corresponding field-four rows. This leaves actual equality,
SL₃(q) or PSL₃(q), or the field-four alternating-seven, triple-cover and
nilpotent odd-kernel SL₂(5) rows. The existential application retains normality
relative to N_G(V₂), He membership and the literal smaller two-core.

This is a reduction of 11.1.2, not its completed second-index conclusion.
The remaining module recognition, Cartan and signalizer exclusions, and the
field-four triangle, belong to qt-d-1222-natural-relative-components.
The preceding rank-one quotient and natural-plane maps belong to
qt-d-1222-natural-flag-cartan, with ultimate discharge by
qt-d-1222-natural-local-geometry. No embedding-list premise remains.

Source: Aschbacher--Smith 11.1.1--11.1.2, printed pp.761--765,
combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

open Chapter1.Section02.LocalModels in
/-- The proved embedding catalogue and full-plane bounds leave only linear,
alternating-seven and nilpotent-extension rows, or actual equality. The
remaining rows are explicit conclusions, not extra source assumptions. -/
theorem second_remaining_models_from_preceding_inputs
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hLK : f.Li 1 ≤ K)
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) :
    f.Li 1 = K ∨
      Source.IsSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree) ∨
      (S.field.degree = 2 ∧
        (IsAlternating (K ⧸ pCore 2 K) 7 ∨ IsAlternatingCover (K ⧸ pCore 2 K) 7 ∨
          HasExtension (K ⧸ pCore 2 K)
            (fun P _ => Group.IsNilpotent P ∧ Odd (Nat.card P))
            (fun Q _ => Source.IsSL Q 2 5))) := by
  by_cases he : f.Li 1 = K
  · exact .inl he
  have hlt := lt_of_le_of_ne hLK he
  have hcatalogue := Embedding.flag_component_alternative D S f 1 hm hK hLK
  cases hcatalogue with
  | equal he => exact .inl he
  | lie h =>
    rcases second_lie_is_linear D S f hK hLK π hπ p hp hact hk h with h | h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  | four hn h =>
    cases h with
    | alternating h => exact .inr (.inr (.inr ⟨hn,.inl h⟩))
    | alternatingCover h => exact .inr (.inr (.inr ⟨hn,.inr (.inl h)⟩))
    | nilpotentExtension h => exact .inr (.inr (.inr ⟨hn,.inr (.inr h)⟩))
    | primeLinear r hr h =>
      have hr2 : r ≠ 2 := by intro h; subst r; norm_num [Source.ExceptionalPrime] at hr
      exact (second_not_primeLinear_of_proper D S f hm hK hlt hr.1
        (hr.1.odd_of_ne_two hr2) π hπ p hp hact hk h).elim
    | linearTwentyFive h =>
      exact (second_not_quadratic_rank_one_of_proper D S f hm hK hlt
        Nat.prime_five (by decide) π hπ p hp hact hk h).elim
    | three u h => exact (second_not_odd_ternary D S f hm hK hLK
        π hπ p hp hact hk Nat.prime_five (by decide) u h).elim
    | m22 h => exact (second_not_small_sporadic D S f hm hK hLK
        π hπ p hp hact hk (.inl h)).elim
    | m22Cover h => exact (second_not_small_sporadic D S f hm hK hLK
        π hπ p hp hact hk (.inr (.inl h))).elim
    | m23 h => exact (second_not_small_sporadic D S f hm hK hLK
        π hπ p hp hact hk (.inr (.inr (.inl h)))).elim
    | hs h => exact (second_not_small_sporadic D S f hm hK hLK
        π hπ p hp hact hk (.inr (.inr (.inr h)))).elim
    | j1 h => exact (second_not_jankoOne D S f hm hK hLK π hπ p hp hact hk h).elim
    | j2 h => exact (second_not_jankoTwo D S f hm hK hLK π hπ p hp hact hk h).elim
    | j4 h => exact (second_not_large_sporadic D S f hm hK hLK
        π hπ p hp hact hk (.inl h)).elim
    | ru h => exact (second_not_large_sporadic D S f hm hK hLK
        π hπ p hp hact hk (.inr h)).elim
    | elementaryExtension r hr h => exact (second_not_elementary_extension D S f hm hK hLK
        hr π hπ p hp hact hk h).elim

open Chapter1.Section02.LocalModels in
/-- Construct the relatively normal containing component and apply the
second-normalizer sieve to its literal smaller two-core quotient. -/
theorem second_exists_normal_component_remaining_models
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) :
    ∃ K : Subgroup G, Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K ∧
      f.Li 1 ≤ K ∧ K ∈ Chapter1.He G ∧
      (f.Li 1 = K ∨
        Source.IsSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree) ∨
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree) ∨
        (S.field.degree = 2 ∧
          (IsAlternating (K ⧸ pCore 2 K) 7 ∨ IsAlternatingCover (K ⧸ pCore 2 K) 7 ∨
            HasExtension (K ⧸ pCore 2 K)
              (fun P _ => Group.IsNilpotent P ∧ Odd (Nat.card P))
              (fun Q _ => Source.IsSL Q 2 5)))) := by
  obtain ⟨K,hK,hLK,hHe,_⟩ := flag_exists_unique_normal_component_of_model D S f 1 hm
  exact ⟨K,hK,hLK,hHe,second_remaining_models_from_preceding_inputs D S f hm hK.1 hLK
    π hπ p hp hact hk⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
