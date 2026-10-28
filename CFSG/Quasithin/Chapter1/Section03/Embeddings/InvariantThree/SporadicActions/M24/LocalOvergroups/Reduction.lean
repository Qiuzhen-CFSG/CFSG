module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.LocalData
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Trio
public import Theory.Mathieu.M24.Properties.Order

/-!
# Reduction of M₂₄ pair placement to a concrete trio stabilizer

For a source pair, permutability and coprime orders make its join a solvable
subgroup of order 9,216 or 27,648. Its index is odd and it is proper. These
are consequences of the supplied pair hypotheses, available to the geometric
placement proof without further assumptions on the pair.

Two independent obligations remain: place this join in a conjugate of the
explicit standard trio stabilizer, and construct the quotient S₃ × L₃(2)
for that stabilizer. The conditional assembly transports the actual quotient
homomorphism through conjugation, preserving surjectivity and its two-group
kernel. It does not establish either obligation or the unqualified local
overgroup theorem.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), citing Aschbacher's *Overgroups of Sylow
subgroups in sporadic groups* (1986); Aschbacher, *Sporadic Groups*, Lemma
20.2, printed p.97; GLS3, Table 5.3e, E₆₄.N(3B).
-/

@[expose] public section

open Subgroup
open Sporadic.Mathieu
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.M24PairAction

/-- The remaining geometric obligation for every source pair. The conjugator
is an element of the fixed Witt-design carrier. -/
def TrioPlacement : Prop :=
  ∀ (S : Sylow 2 M24) (R : Subgroup M24), PairInput S R →
    ∃ g : M24, R ⊔ (S : Subgroup M24) ≤ conjugateTrioStabilizer g

/-- The remaining quotient calculation for one specified geometric subgroup.
No splitting, order or simplicity certification is required by this contract. -/
def StandardTrioQuotient : Prop :=
  ∃ f : trioStabilizer standardTrio →* LocalQuotient,
    Function.Surjective f ∧ IsPGroup 2 f.ker

/-- The two possible orders of the actual permuting product. -/
theorem pair_product_orders {S : Sylow 2 M24} {R : Subgroup M24}
    (h : PairInput S R) :
    Nat.card (R ⊔ (S : Subgroup M24) : Subgroup M24) = 9216 ∨
      Nat.card (R ⊔ (S : Subgroup M24) : Subgroup M24) = 27648 := by
  have hfac : Nat.factorization 244823040 2 = 10 := by
    have hzero : padicValNat 2 239085 = 0 :=
      padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
    rw [Nat.factorization_def 244823040 Nat.prime_two,
      show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num,
      padicValNat_base_pow_mul (by norm_num) (by norm_num) 10, hzero]
  have hS : Nat.card S = 1024 := by
    rw [S.card_eq_multiplicity, m24_order, hfac]
    norm_num
  rw [EvenRankTwo.product_card h, hS]
  rcases h.oddComplement with ⟨_, hc⟩ | ⟨_, hc, _⟩ <;> rw [hc] <;> norm_num

/-- The pair product is a proper solvable subgroup of odd index, with both
possible orders retained. No extraspecial-complement case is discarded. -/
theorem pair_product_data {S : Sylow 2 M24} {R : Subgroup M24}
    (h : PairInput S R) :
    Group.IsSolvable (R ⊔ (S : Subgroup M24) : Subgroup M24) ∧
      R ⊔ (S : Subgroup M24) ≠ ⊤ ∧
      ¬ 2 ∣ (R ⊔ (S : Subgroup M24) : Subgroup M24).index ∧
      (Nat.card (R ⊔ (S : Subgroup M24) : Subgroup M24) = 9216 ∨
        Nat.card (R ⊔ (S : Subgroup M24) : Subgroup M24) = 27648) := by
  refine ⟨EvenRankTwo.product_solvable h, EvenRankTwo.product_ne_top h, ?_,
    pair_product_orders h⟩
  exact fun hd => S.not_dvd_index (hd.trans (index_dvd_of_le le_sup_right))

/-- A quotient of the standard stabilizer transports to every conjugate
stabilizer, including its actual two-group kernel. -/
theorem quotient_of_standard_trio (hq : StandardTrioQuotient) (g : M24) :
    ∃ f : conjugateTrioStabilizer g →* LocalQuotient,
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  obtain ⟨f, hf, hk⟩ := hq
  let e := conjugateTrioStabilizerEquiv g
  refine ⟨f.comp e.symm.toMonoidHom, ?_, ?_⟩
  · intro x
    obtain ⟨y, hy⟩ := hf x
    refine ⟨e y, ?_⟩
    change f (e.symm (e y)) = x
    rw [e.symm_apply_apply, hy]
  exact hk.comap_of_injective e.symm.toMonoidHom e.symm.injective

/-- Conditional assembly: both geometric placement and the standard
stabilizer's quotient still have to be proved. -/
theorem localOvergroups_of_trio_placement
    (hp : TrioPlacement) (hq : StandardTrioQuotient) : LocalOvergroups := by
  intro S R h
  obtain ⟨g, hg⟩ := hp S R h
  exact ⟨conjugateTrioStabilizer g, le_sup_right.trans hg, le_sup_left.trans hg,
    quotient_of_standard_trio hq g⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.M24PairAction

end
