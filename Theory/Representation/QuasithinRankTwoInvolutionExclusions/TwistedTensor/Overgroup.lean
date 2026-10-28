module

public import Theory.SpecificGroups.PSL2.OuterInvolutionFormula
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Ambient involutions lie in the marked SL₂(8) component

Conjugation on F*(H), transported through the actual SL₂(8) isomorphism, gives
an automorphism whose square is one. The proved semilinear automorphism theorem
forces an outer involution to have even field degree, excluding it in degree
three. An inner conjugation puts the original element in F*(H) C_H(F*(H));
the generalized-Fitting centralizer theorem absorbs the centralizer.

Thus the permitted field overgroup introduces no new involutions. No containment
of involutions is inferred merely from a group-family name, and no ambient
faithfulness or centralizer premise remains to be discharged.

Source: Aschbacher–Smith, G.11.2(11), printed p.364 (PDF p.375), and the
case-(11) exclusion in 6.2.19, printed p.691 (PDF p.708).
-/

@[expose] public section

open scoped MatrixGroups
open Theory.GroupTheory Subgroup
namespace Representation.RankTwo.TwistedTensor

/-- The defining field of order eight. -/
abbrev F := GaloisField 2 3

variable {H : Type*} [Group H] [Finite H]

/-- Every element of order dividing two lies in the actual generalized Fitting subgroup. -/
theorem involution_mem_generalizedFitting
    (e : generalizedFitting H ≃* SL(2,F)) (g : H) (hg : g ^ 2 = 1) :
    g ∈ generalizedFitting H := by
  let L := generalizedFitting H
  let a : H →* MulAut SL(2,F) :=
    (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  have ha : a g ^ 2 = 1 := by rw [← map_pow, hg, map_one]
  have hin : a g ∈ MulAut.innerSubgroup SL(2,F) := by
    by_contra hout
    have hev := (Theory.PSL2.sl2_outer_involution_formula (r := 3) (by decide)
      (GaloisField.card 2 3 (by decide)) (a g) ha hout).1
    norm_num at hev
  change MulAut.congr e (MulAut.conjNormal g) ∈ MulAut.innerSubgroup _ at hin
  rw [← MulAut.map_innerSubgroup_congr e, Subgroup.mem_map_equiv] at hin
  simp only [MulEquiv.symm_apply_apply] at hin
  have hm : g ∈ (MulAut.innerSubgroup L).comap MulAut.conjNormal := hin
  rw [MulAut.conjNormal_comap_innerSubgroup] at hm
  exact (sup_le le_rfl (centralizer_generalizedFitting_le H)) hm

end Representation.RankTwo.TwistedTensor
