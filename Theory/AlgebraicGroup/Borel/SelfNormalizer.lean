module

public import Theory.AlgebraicGroup.Borel.SelfNormalizer.TorusCommutator

/-!
# Dimension induction for Borel self-normalization

This module assembles the reductions in Borel, *Linear Algebraic Groups*,
Theorem 11.16. After conjugating a maximal torus inside the Borel, it suffices
to consider an element normalizing both. Its fixed subgroup in the torus is
either finite, or has positive-dimensional identity component. The finite
case forces `B = G`; the other case reduces to a central quotient or a proper
connected torus centralizer and uses strictly smaller dimension.

The two geometric branch theorems remain explicit hypotheses here. In
particular, this conditional induction does not yet establish unconditional
self-normalization, nor GLS3 Theorem 1.6.3. Genuine completeness of the Borel
homogeneous space is required by the finite case.

Sources: `refs/KGroup/Bor1/Chapter4.tex`, Theorem 11.16, lines 213–230;
`refs/KGroup/GLS3/Chapter1.tex`, the Borel-normalizer clause of Theorem 1.6.3.
-/

universe u

namespace Theory.AlgebraicGroup.BorelSelfNormalizer

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Dimension induction closes the Borel normalizer proof once both genuine
fixed-torus branches have been proved uniformly. `hfinite` is source case
(iii); `hinfinite` comprises cases (i) and (ii) and may use only strictly
smaller-dimensional self-normalization. -/
public theorem normalizer_eq_of_fixed_torus_cases
    (hfinite : ∀ (H : Variety k) [AlgebraicGroup H], Variety.IsConnected H →
      ∀ (B T : ClosedSubgroup H), IsBorelSubgroup B → IsMaximalTorus T → T ≤ B →
      ∀ n : Variety.Point H,
        n ∈ B.normalizer.toSubgroup → n ∈ T.normalizer.toSubgroup →
        (fixedTorusPoints T n).Finite → B = ClosedSubgroup.top)
    (hinfinite : ∀ (H : Variety k) [AlgebraicGroup H], Variety.IsConnected H →
      SmallerDimension H →
      ∀ (B T : ClosedSubgroup H), IsBorelSubgroup B → IsMaximalTorus T → T ≤ B →
      ∀ n : Variety.Point H,
        n ∈ B.normalizer.toSubgroup → n ∈ T.normalizer.toSubgroup →
        ¬(fixedTorusPoints T n).Finite → n ∈ B.toSubgroup)
    {G : Variety k} [AlgebraicGroup G] (hG : Variety.IsConnected G)
    (B T : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (hT : IsMaximalTorus T) (hTB : T ≤ B) :
    B.normalizer = B := by
  induction hdim : Cardinal.toNat (Variety.dimension G)
      using Nat.strong_induction_on generalizing G with
  | h d ih =>
      have hsmaller : SmallerDimension G := by
        intro H _ hHdim hH C S hC hS hSC
        have hd : Cardinal.toNat (Variety.dimension H) < d := by
          rw [← hdim]
          exact Cardinal.toNat_lt_toNat hHdim (variety_dimension_lt_aleph0 G)
        exact ih _ hd hH C S hC hS hSC rfl
      apply normalizer_eq_of_simultaneous_normalizer_le hB hT hTB
      intro n hn
      by_cases hfix : (fixedTorusPoints T n).Finite
      · rw [hfinite G hG B T hB hT hTB n hn.1 hn.2 hfix]
        exact Subgroup.mem_top n
      · exact hinfinite G hG hsmaller B T hB hT hTB n hn.1 hn.2 hfix

end Theory.AlgebraicGroup.BorelSelfNormalizer
