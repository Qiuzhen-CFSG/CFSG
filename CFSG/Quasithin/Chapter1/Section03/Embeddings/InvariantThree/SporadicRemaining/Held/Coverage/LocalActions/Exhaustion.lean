module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Reductions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import Theory.SpecificGroups.Held.Model.Basic
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalSubgroups
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.Residual
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Candidates
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion

/-!
# Source assembly for locally placed Held pairs

Permutability and the source odd-complement alternatives force the pair
product to have only the primes two and three. Its relative index in a local
overgroup is odd because it contains an ambient Sylow two-subgroup. Local
subgroup coverage therefore puts it in a candidate product. The latter has
order 9216, excluding the order-27 branch of the original source input.
Sylow conjugacy and the resulting relative normalizer factorization align both
members of the pair by one element of the original local overgroup.

The unconditional `pair_conjugate` theorem discharges all concrete premises
using the kernel-checked candidate orders and local subgroup cover. The
larger local overgroup itself has no asserted nondivisibility by 27.

Sources: Aschbacher–Smith, printed pp.509–511; GLS3 Table 5.3p. This is the
retained Held branch, not the unmodified assertion of Proposition 1.3.4.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs
namespace LocalActions

open Held.LocalPairs.PairCoverage
open Held.LocalPairs.PairCoverage.LocalActions
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion

/-- The smaller candidate product excludes the extraspecial branch. The
order of the whole local overgroup cannot be used for this argument. -/
theorem pair_card_nine_of_candidate_containment (horders : CandidateOrders)
    {S : Sylow 2 Held.He} {R : Subgroup Held.He} (h : PairInput S R)
    (i : Bool) (j : Fin 2) (hR : R ≤ candidateProduct i j) :
    Nat.card R = 9 := by
  rcases h.oddComplement with ⟨_, hc⟩ | ⟨_, hc, _⟩
  · exact hc
  · have hd := card_dvd_of_le hR
    rw [hc, (horders i j).2.2] at hd
    norm_num at hd

/-- The finite subgroup cover and candidate orders
suffice for the exact simultaneous-conjugacy contract, including order 27. -/
theorem pair_conjugate_of_calculations (horders : CandidateOrders)
    (hcover : LocalProductCover)
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He)
    (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i) :
    ∃ (j : Fin 2) (g : Held.He), g ∈ localOvergroup i ∧
      (S : Subgroup Held.He).map (MulAut.conj g).toMonoidHom = candidateTwo i j ∧
      R.map (MulAut.conj g).toMonoidHom = candidateOdd i j := by
  have hi : ¬ 2 ∣ (R ⊔ (S : Subgroup Held.He)).relIndex (localOvergroup i) := by
    intro hd
    exact S.not_dvd_index (hd.trans
      ((relIndex_dvd_index_of_le hplace).trans (index_dvd_of_le le_sup_right)))
  obtain ⟨j, g, hg, hK⟩ := hcover i _ hplace hi
    (fun _ hp hd => EvenRankTwo.product_prime_divisors h hp hd)
  let e := MulAut.conj g
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let P := R.map e.toMonoidHom
  have hT : (T : Subgroup Held.He) ≤ candidateProduct i j :=
    (map_mono le_sup_right).trans hK
  have hP : P ≤ candidateProduct i j := (map_mono le_sup_left).trans hK
  have hp : PairInput T P := pairInput_of_equiv h e
  obtain ⟨a, ha, hTa, hPa⟩ := pair_conjugate_in_candidate horders i j T P hT hP
    (pair_card_nine_of_candidate_containment horders hp i j hP)
  refine ⟨j, a * g, (localOvergroup i).mul_mem
    (candidateProduct_le_localOvergroup i j ha) hg, ?_, ?_⟩
  · change ((S : Subgroup Held.He).map e.toMonoidHom).map
      (MulAut.conj a).toMonoidHom = candidateTwo i j at hTa
    rw [map_map] at hTa
    exact hTa
  · change (R.map e.toMonoidHom).map (MulAut.conj a).toMonoidHom = candidateOdd i j at hPa
    rw [map_map] at hPa
    exact hPa

/-- The source Sylow context supplies the common ambient Sylow order after
one local placement; all four even candidates are then ambient Sylow groups. -/
theorem candidateTwo_sylow_of_calculations (horders : CandidateOrders)
    (hcover : LocalProductCover) (i : Bool) (S : Sylow 2 Held.He)
    (R : Subgroup Held.He) (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i)
    (i' : Bool) (j' : Fin 2) :
    ∃ T : Sylow 2 Held.He, (T : Subgroup Held.He) = candidateTwo i' j' := by
  obtain ⟨j, g, _, hS, _⟩ := pair_conjugate_of_calculations horders hcover i S R h hplace
  have hcS : Nat.card S = 1024 := by
    calc
      Nat.card S = Nat.card ((S : Subgroup Held.He).map
          (MulAut.conj g).toMonoidHom) :=
        Nat.card_congr ((MulAut.conj g).subgroupMap (S : Subgroup Held.He)).toEquiv
      _ = 1024 := by rw [hS, (horders i j).1]
  exact candidateTwo_sylow_of_sylow_card horders S hcS i' j'

/-- Exhaustive simultaneous conjugacy of locally placed Held pairs. The same
element of the original local overgroup carries both subgroups to the literal
candidates. No catalogue, plane, realization, or normalizer premise remains. -/
theorem pair_conjugate
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He)
    (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i) :
    ∃ (j : Fin 2) (g : Held.He), g ∈ localOvergroup i ∧
      (S : Subgroup Held.He).map (MulAut.conj g).toMonoidHom = candidateTwo i j ∧
      R.map (MulAut.conj g).toMonoidHom = candidateOdd i j :=
  pair_conjugate_of_calculations candidateOrders localProductCover i S R h hplace

/-- Local placement rules out the order-27 complement, by the certified
smaller candidate products rather than the order of the local overgroup. -/
theorem pair_card_nine
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He)
    (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i) :
    Nat.card R = 9 := by
  obtain ⟨j, g, _, _, hR⟩ := pair_conjugate i S R h hplace
  calc
    Nat.card R = Nat.card (R.map (MulAut.conj g).toMonoidHom) :=
      Nat.card_congr ((MulAut.conj g).subgroupMap R).toEquiv
    _ = 9 := by rw [hR, (candidateOrders i j).2.1]

/-- An actual locally placed pair makes all four even candidates Sylow in
Held. This uses the inherited Sylow context and no global Held-order theorem. -/
theorem candidateTwo_sylow
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He)
    (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i)
    (i' : Bool) (j' : Fin 2) :
    ∃ T : Sylow 2 Held.He, (T : Subgroup Held.He) = candidateTwo i' j' :=
  candidateTwo_sylow_of_calculations candidateOrders localProductCover i S R h hplace i' j'

end LocalActions
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs
