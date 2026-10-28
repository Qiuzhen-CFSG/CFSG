module

public import Theory.GroupAction.AutomorphismNormalizer
public import Theory.GroupAction.ElementarySylowFixerBound
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.Quasithin.Rank
public import Theory.SpecificGroups.Rudvalis.Model.Primitive
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.SylowCenters
public import Theory.SpecificGroups.Rudvalis.Model.LowCentralizers.Center
public import Theory.SpecificGroups.Rudvalis.Multiplier.OddLocal.Three

/-!
# Rudvalis facts for the ordinary component argument

The certified nonabelian subgroup of order 27 forces three-rank at least two.
The point-stabilizer and permutation-normalizer theorems make every
automorphism inner when simplicity is inherited from a source component.
The center of a Sylow two-subgroup has order two, giving the elementary
pointwise fixer bound. This supplies the facts needed for the same centralizer
argument as the other ordinary sporadic rows.

The automorphism proof is adapted from the existing
`Chapter1/Section03/Embeddings/ComponentReduction/OuterModels/AlternatingSporadic/Rudvalis`
argument, keeping this intrinsic extension below CFSG.
Source: GLS3 Table 5.3r and Aschbacher--Smith 15.1.22, printed p.1100.
-/

public section
namespace Rudvalis
open Subgroup Theory.GroupTheory Theory.GroupAction
open scoped IsMulCommutative

/-- The actual nonabelian order-27 subgroup rules out three-rank at most one. -/
theorem three_rank_ge_two : 2 ≤ primeRank 3 Model := by
  obtain ⟨P, hcard, hnon⟩ := Multiplier.OddLocal.three_subgroup
  have hp : IsPGroup 3 P := IsPGroup.of_card hcard
  by_contra hh
  have hr : primeRank 3 P ≤ 1 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 P.subtype P.subtype_injective).trans (by omega)
  let : IsCyclic P := hp.isCyclic_of_odd_of_elementary_card_le (by decide)
    (fun E hE => by
      let : IsElementaryAbelian 3 E := hE
      exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr E)
  exact hnon inferInstance

/-- Simplicity inherited from the source suffices for the proved realization. -/
theorem component_conj_surjective [IsSimpleGroup Model] :
    Function.Surjective (MulAut.conj : Model →* MulAut Model) := by
  let : MulAction.IsPretransitive modelSubgroup (Fin 4060) := model_isPretransitive
  exact Subgroup.conj_surjective_of_stabilizers_of_normalizer modelSubgroup 0
    outer_stabilizer_map_eq outer_permutation_normalizer_eq

/-- In particular the outer group is a two-group (indeed it is trivial). -/
theorem outer_isPGroup_two [IsSimpleGroup Model] : IsPGroup 2 (MulAut.Outer Model) := by
  let : Subsingleton (MulAut.Outer Model) := QuotientGroup.subsingleton_iff.mpr
    (MonoidHom.range_eq_top.mpr component_conj_surjective)
  exact fun x => ⟨0, Subsingleton.elim _ _⟩

/-- The elementary pointwise Sylow-fixer bound, using inherited simplicity. -/
theorem elementary_sylow_fixer_card_le_two [IsSimpleGroup Model]
    (S : Sylow 2 Model) (A : Subgroup (MulAut Model)) [IsElementaryAbelian 2 A]
    (hfix : ∀ a ∈ A, ∀ x ∈ S, a x = x) : Nat.card A ≤ 2 := by
  let : IsCyclic (center S) := isCyclic_of_prime_card (InvolutionCentralizers.sylow_center_card S)
  apply elementary_sylow_fixer_card_le_two_of_inner S LowCentralizers.model_center_eq_bot _ A hfix
  intro a _ _
  obtain ⟨g, hg⟩ := component_conj_surjective a
  exact ⟨g, hg.symm⟩

end Rudvalis
