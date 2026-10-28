module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.Conjugation
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.Centralizer.Reduction

/-!
# Transfer of the common-subgroup certificates to large J₄ centralizers

The actual centralizer of K embeds in the centralizer of [T,[T,T]] when the
common-subgroup coverage certificate places [T,[T,T]] in K. Its certified
binary commutant flag therefore makes C_Model(K) a two-group, so three cannot
divide its order. The proof uses the literal matrix carrier and subgroup
inclusion. It requires no ambient group order or simplicity certification.

The theorem below retains both concrete certificate obligations as premises.
The unconditional `fixedTwoLargeCentralizerThreeFree` still requires their
construction. Source context: Aschbacher–Smith, proof of Proposition 1.3.4,
printed p.511/PDF p.528 of `refs/quasithin.pdf`, citing Aschbacher (1986).
-/

@[expose] public section

open Subgroup
open Janko4.OuterReduction.OddIndex
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- The two independent concrete certificates imply the requested centralizer bound. -/
theorem fixedTwoLargeCentralizerThreeFree_of_commonCommutator
    (hcover : FixedTwoThirdCommutatorCoverage) (hflag : FixedTwoThirdCommutantFlag) :
    FixedTwoLargeCentralizerThreeFree := by
  intro _ _ _ _ _ K hKT hKN hindex _
  have hC : centralizer (K : Set Janko4.Model) ≤
      centralizer (fixedTwoThirdCommutator : Set Janko4.Model) :=
    centralizer_le (hcover K hKT hKN hindex)
  have hP := (fixedTwoThirdCommutator_centralizer_isPGroup_of_flag hflag).of_injective
    (inclusion hC) (inclusion_injective hC)
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn]
  exact fun h => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
