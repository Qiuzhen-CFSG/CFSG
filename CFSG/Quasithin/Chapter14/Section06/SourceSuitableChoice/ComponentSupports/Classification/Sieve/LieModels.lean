module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.Exceptional
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Models

/-!
# The Lie-type remainder of the terminal component sieve

The A₇ and M₂₂ exclusions apply to the actual relative component and its
literal two-core quotient. That quotient is simple and perfect, hence
centerless. Transporting the broader F.9.18 list through its central quotient
therefore leaves only the characteristic-two Lie-type rows; the genuine
central-three M₂₂ cover is also excluded, by the same central-quotient map.
All alternatives retain actual model isomorphisms.

This is the first reduction of Aschbacher--Smith 14.6.20, printed p.1037.
The broader F.9.18 premise must still be instantiated on the Chapter14 setup
by qt-e-suitable-component-supports; its Chapter13 source producer does not
supply that change of setup automatically. Original 14.6.18 remains with
qt-e-14625-source. The Borel, high-rank and diagram steps are not asserted here.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08.Components.Models
variable {G : Type*} [Group G] [Finite G]

/-- The actual characteristic-two model rows left after the exceptional sieve.
The parameters and derived groups are those of the original F.9.18 list. -/
@[expose] def LieQuotientModels (D : Type*) [Group D] : Prop :=
  ClassificationModels.IsBenderModel D ∨
  (∃ n : ℕ, 1 ≤ n ∧ ClassicalGroup.IsPSL D 3 (2 ^ n)) ∨
  (∃ n : ℕ, 1 ≤ n ∧ IsSp4DerivedAt D (2 ^ n)) ∨
  (∃ n : ℕ, 1 ≤ n ∧ IsG2DerivedAt D (2 ^ n)) ∨
  ClassicalGroup.IsPSL D 4 2 ∨ ClassicalGroup.IsPSL D 5 2

/-- The original relative component has a Lie-type two-core quotient once the
broader F.9.18 model input is supplied; no exceptional or normality callback remains. -/
theorem source_component_lie_models_of_f918
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hm : F918Models (K ⧸ pCore 2 K)) : LieQuotientModels (K ⧸ pCore 2 K) := by
  have hz := source_component_quotient_center_eq_bot
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
  let a := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm
  rcases hm with ⟨hm,_⟩ | hm | hm
  · cases hm with
    | bender hb =>
      apply Or.inl
      cases hb with
      | linear n hn hi => exact .linear n hn (hi.of_mulEquiv a)
      | unitary n hn hi => exact .unitary n hn (hi.of_mulEquiv a)
      | suzuki m hm hi => exact .suzuki m hm (hi.map (a.trans ·))
    | linear_three n hn hi => exact Or.inr (Or.inl ⟨n,hn,hi.of_mulEquiv a⟩)
    | symplectic n hn hi => exact Or.inr (Or.inr (Or.inl ⟨n,hn,hi.of_mulEquiv a⟩))
    | g2 n hn hi => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n,hn,hi.of_mulEquiv a⟩)))
    | linear_four hi => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hi.of_mulEquiv a)))))
    | linear_five hi => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hi.of_mulEquiv a)))))
    | alternating_seven he =>
      exact (source_component_a7_false hG T hempty hM hunique hmany hcard e hab hsolv
        H hH K hKH hK (a.trans he.some)).elim
  · obtain ⟨em⟩ := hm
    exact (source_component_m22_false hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK em).elim
  · obtain ⟨_,_,⟨em⟩⟩ := hm
    exact (source_component_m22_false hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK (a.trans em)).elim
end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
