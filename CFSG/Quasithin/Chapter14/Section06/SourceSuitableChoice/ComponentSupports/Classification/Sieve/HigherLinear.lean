module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.ImageRank
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.NonnormalModels
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.SolvableRank
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Excluding the higher linear rows in the terminal component sieve

In dimensions four and five, the actual binary flag supplies a solvable
Sylow overgroup of three-rank two invariant under every Sylow-preserving
automorphism. Its original component lift lies in M by 14.6.18, contrary
to the three-rank-one bound on M intersect Mc. Coefficientwise field
transport applies this to the field-independent PSL predicates.

The final consumers remove both higher-rank rows from the proved F.9.18
catalogue, including at the unchanged terminal group Mc. The remaining
rank-one and larger-field exclusions and support assembly stay with
qt-e-suitable-component-supports. Original 14.6.18 remains with
qt-e-14625-source.

Source: Aschbacher--Smith 14.6.20, printed p.1037, the product of the
end-node minimal parabolics.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08.Components.Models
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hsolv

/-- The two higher binary linear models are excluded without requiring
relative normality of the original component. -/
theorem source_component_higher_binary_linear_false
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.OuterCyclic.LinearGroup n) : False := by
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup n) :=
    Finite.of_surjective eK eK.surjective
  obtain ⟨P,hP⟩ := source_component_sylow T H K hH.1.2 hKH hK
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  let Pq := P.mapSurjective hq
  have hex : ∃ J : Subgroup (BinaryLinear.OuterCyclic.LinearGroup n),
      (Pq : Subgroup _) ≤ J ∧ Group.IsSolvable J ∧ primeRank 3 J = 2 ∧
      ∀ a : MulAut (BinaryLinear.OuterCyclic.LinearGroup n),
        (Pq : Subgroup _).map a.toMonoidHom = Pq → J.map a.toMonoidHom = J := by
    rcases hn with rfl | rfl
    · exact BinaryLinear.InvariantNodeActions.exists_invariant_solvable_rank_two_four Pq
    · exact BinaryLinear.InvariantNodeActions.exists_invariant_solvable_rank_two_five Pq
  obtain ⟨J,_,hs,hr,hinv⟩ := hex
  let := hs
  have hb := source_component_invariant_solvable_threeRank_le_one
    hG T hempty hM hunique hmany hcard e hsolv H hH K hKH hK eK P hP J hinv
  omega

/-- The exclusion retains the actual field-independent PSL isomorphism. -/
theorem source_component_not_higher_binary_psl
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2 := by
  rintro ⟨F,_,_,hF,⟨a⟩⟩
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let b := Atlas.fieldEquivPSL n f
  let c := BinaryLinear.OuterCyclic.projectiveEquivLinear
    (show 0 < n from by rcases hn with rfl | rfl <;> decide)
  exact source_component_higher_binary_linear_false hG T hempty hM hunique hmany hcard e hsolv
    H hH K hKH hK hn (a.trans (b.trans c))

/-- The actual Lie models remaining after all exceptional and higher-rank
exclusions. No field-size assertion is built into the rank-one branch. -/
@[expose] def LowRankLieQuotientModels (D : Type*) [Group D] : Prop :=
  ClassificationModels.IsBenderModel D ∨
  (∃ n : ℕ, 1 ≤ n ∧ ClassicalGroup.IsPSL D 3 (2 ^ n)) ∨
  (∃ n : ℕ, 1 ≤ n ∧ IsSp4DerivedAt D (2 ^ n)) ∨
  (∃ n : ℕ, 2 ≤ n ∧ IsG2DerivedAt D (2 ^ n))

/-- Apply the invariant flags to the complete, already instantiated F.9.18
input on the original H and K. -/
theorem source_component_low_rank_lie_models
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    LowRankLieQuotientModels (K ⧸ pCore 2 K) := by
  have hh := source_component_remaining_lie_models hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK
  rcases hh with hb | hl | hs | hg | h4 | h5
  · exact Or.inl hb
  · exact Or.inr (Or.inl hl)
  · exact Or.inr (Or.inr (Or.inl hs))
  · exact Or.inr (Or.inr (Or.inr hg))
  · exact (source_component_not_higher_binary_psl hG T hempty hM hunique hmany hcard e hsolv
      H hH K hKH hK (Or.inl rfl) h4).elim
  · exact (source_component_not_higher_binary_psl hG T hempty hM hunique hmany hcard e hsolv
      H hH K hKH hK (Or.inr rfl) h5).elim

/-- The terminal low-rank catalogue keeps H=Mc and has no extra model,
normality, rank or flag premise. -/
theorem terminal_component_low_rank_lie_models
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    LowRankLieQuotientModels (K ⧸ pCore 2 K) :=
  source_component_low_rank_lie_models hG T hempty hM hunique hmany hcard e hsolv hab Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
