module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization.Degree.FiberCount.Correspondence
public import Theory.SpecificGroups.PSL2.OddInvolutionPairs

/-!
# The exact linear mixed-involution fiber count

The explicit correspondence `(s,v) ↦ (uv,s)` identifies the actual Thompson
fiber with ordered local involution pairs of odd-order product. Transport
through the supplied matrix isomorphism gives q²−1 choices of first factor
and q(q−1)+1 choices of second factor, including the equal-factor pair.
This discharges the fiber-count premise of the linear coset-degree assembly;
the single shearing fusion and selected centralizer collapse remain exactly
the permitted inputs. No coset degree or ambient two-class exhaustion is used.

Source: GLS, Volume 4, Chapter 2, Lemma 12.8(a),
`refs/KGroup/GLS4/Chapter2.tex`, the calculation of `a(u)`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII TwoInvolutionClassOrder
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The exact source fiber count from one shearing fusion and the actual local
PSL₂ model. Neither minimality nor containment of the distinguished closure
is needed beyond the stated local strong-embedding hypotheses. -/
public theorem linear_kappa_of_one_fusion
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (huJ : u ∈ centralizer (residualGenerated M z t : Set G))
    (hu : PFAppendixIII.IsInvolution u)
    (hcollapse : centralizerClosure Z u = residualGenerated M z t)
    (hshear : IsConj u (u * z)) :
    kappa z u u = (2 ^ n - 1) * (2 ^ n + 1) * (2 ^ n * (2 ^ n - 1) + 1) := by
  rw [linear_kappa_eq_odd_pairs h r hz hzM ht htM hL huJ hu hcollapse hshear]
  let f : {p : residualGenerated M z t × residualGenerated M z t //
      orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))} ≃
      {p : MatrixGroups.PSL2BinaryMatrixGroup n × MatrixGroups.PSL2BinaryMatrixGroup n //
      orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))} :=
    Equiv.subtypeEquiv (Equiv.prodCongr e.toEquiv e.toEquiv) (by
      intro p
      change (_ ∧ _ ∧ _) ↔ (orderOf (e p.1) = 2 ∧ orderOf (e p.2) = 2 ∧
        Odd (orderOf (e p.1 * e p.2)))
      simp only [← map_mul, e.orderOf_eq])
  rw [Nat.card_congr f, Theory.PSL2.card_odd_involution_pairs_char_two,
    Converse.card_binaryGaloisField n (by omega)]
end BenderSuzuki.ZD
