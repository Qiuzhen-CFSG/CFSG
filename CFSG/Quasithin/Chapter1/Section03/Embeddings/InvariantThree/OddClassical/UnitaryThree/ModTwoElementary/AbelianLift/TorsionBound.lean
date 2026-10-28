module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.AbelianLift.CubeLine
public import Theory.Representation.CubicTorsionDegreeThree

/-!
# The cubic torsion bound for abelian SU₃ lifts

The cube-one subgroup of an abelian full preimage in SU₃ acts faithfully by
its actual degree-three matrices, all with determinant one. Since the matrix
field has cardinality p² for a prime p > 3, its characteristic differs from
three. The determinant-one cubic torsion bound gives order at most nine.

This supplies the matrix input to the intrinsic cube-one line construction.
It applies to every stored Hermitian form; its proof needs no restriction on
p modulo three and no choice of standard Gram matrix.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), and the abelian argument underlying A.3.21(c), printed pp.55–56
(PDF pp.66–67), in `refs/quasithin.pdf`.
-/

public section

open scoped IsMulCommutative

open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.AbelianLift

/-- Cubic torsion in every abelian special-unitary lift has order at most nine. -/
theorem cubic_torsion_bound {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    CubicTorsionBound p := by
  intro E _ _ J hcard _ U _
  let _ : Fact p.Prime := ⟨hp⟩
  let _ := Fintype.ofFinite E
  let _ : CharP E p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  have hthree : (3 : E) ≠ 0 :=
    (CharP.cast_eq_zero_iff E p 3).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hp3)
  let f : cubeSubgroup J U →* GL (Fin 3) E :=
    J.specialSubgroup.subtype.comp
      ((U.comap J.specialToProjective).subtype.comp (cubeSubgroup J U).subtype)
  apply Representation.card_le_nine_of_faithful_generalLinear_cube_det_one f
    (J.specialSubgroup.subtype_injective.comp
      ((U.comap J.specialToProjective).subtype_injective.comp
        (cubeSubgroup J U).subtype_injective)) hthree
  · intro x
    exact Subtype.ext x.property
  · intro x
    exact x.val.val.property.2

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.AbelianLift
