module
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Descent
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.RankOne.Faithfulness

/-!
# Odd triality pinned rank-one embeddings and quotient faithfulness

The integral Geck construction supplies the four pinned SL₂ maps and the
commuting arm curves. The central simple-root map and the three-arm Frobenius
diagonal remain injective after elementary restriction and the actual central
quotient. The scalar images are tested on adjacent fixed root elements; this
includes characteristic three and every positive field exponent, without an
SL₂ perfectness assumption.

The applications below identify the literal fundamental subgroup, certify its
scalar involution, and supply the faithful complementary map to the existing
residual-rank theorem. The complementary commutation input belongs to the
separate centralizer-geometry assembly.

Sources: GLS3 §§2.4 and 2.6, especially Proposition 2.6.2
(`refs/KGroup/GLS3/chapter2.tex`); Aschbacher–Smith A.2.17, printed p.39
of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.OddFundamentalCentralizer.RankOne

/-- The source fundamental subgroup itself, with the literal central-quotient map. -/
def fundamentalEquiv (P : Parameters) (hp : Odd P.prime) :
    SL(2, GaloisField P.prime P.exponent) ≃* fundamental P :=
  OddFundamentalCentralizer.fundamentalEquiv (pinnedRankOneMaps P)
    (fundamentalHom_injective P hp)

/-- The marked scalar survives the central quotient as an involution. -/
theorem fundamental_scalar_involution (P : Parameters) (hp : Odd P.prime) :
    orderOf (fundamentalHom (pinnedRankOneMaps P) (-1)) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow]
    simp
  · intro h
    have he : (-1 : SL(2, GaloisField P.prime P.exponent)) = 1 :=
      fundamentalHom_injective P hp (h.trans (map_one _).symm)
    have heE := congrArg (sl2BaseEmbedding P) he
    change SpecialLinearGroup.map _ (-1) = SpecialLinearGroup.map _ 1 at heE
    rw [map_neg_one, map_one] at heE
    have he1 : (-1 : ExtensionField P) = 1 := by
      have he0 := congrArg (fun A : SL(2, ExtensionField P) => A.val 0 0) heE
      simpa using he0
    exact two_ne_zero P hp (by linear_combination -he1)

/-- Conjugation by the specified highest-root Weyl word preserves faithfulness. -/
theorem complementHom_injective (P : Parameters) (hp : Odd P.prime) :
    Function.Injective (complementHom (pinnedRankOneMaps P) (armRootCommutation P)) :=
  (MulAut.conj (highestWeyl (pinnedRankOneMaps P) (armRootCommutation P))⁻¹).injective.comp
    (armsHom_injective P hp)

/-- The new faithful cubic embedding discharges the injection premise of the
literal residual-rank consumer. Its commuting-root premise remains with the
centralizer-geometry owner. -/
theorem three_mul_exponent_le_residual_rank (P : Parameters) (hp : Odd P.prime)
    (hcomm : ∀ a b, Commute (fundamentalHom (pinnedRankOneMaps P) a)
      (complementHom (pinnedRankOneMaps P) (armRootCommutation P) b)) :
    3 * P.exponent ≤ primeRank P.prime (residual P) :=
  OddFundamentalCentralizer.three_mul_exponent_le_residual_rank
    (pinnedRankOneMaps P) _ hcomm (complementHom_injective P hp)

end Triality.Standard.OddFundamentalCentralizer.RankOne
