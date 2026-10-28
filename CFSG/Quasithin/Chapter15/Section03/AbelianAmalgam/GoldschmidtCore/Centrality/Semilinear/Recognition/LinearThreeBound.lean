module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.RankComparison
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order

/-!
# The small Sylow bound in the degree-three branch

The actual upper unitriangular subgroup of SL₃(2ⁿ) has order 2^(3n).
Transport it through the supplied group embedding and contain it in a Sylow
of the ambient group. An ambient Sylow order at most 128 forces 3n ≤ 7;
odd positive n is therefore one. The resulting SL₃(2) identification is
transported from the original representation model via a field equivalence,
never inferred merely from the order of a group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the B.5.1 /
F.6.18 comparison used in the repaired 15.3.68 argument, pp.1154–1155.
The thirteen-row classification must supply the ambient Sylow bound.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {D : Type u} [Group D] [Finite D]

/-- The concrete unipotent subgroup bounds the field degree for any actual
SL₃ embedding in a group with small Sylow two-subgroups. -/
theorem linearThree_degree_eq_one (F : BinaryField) (ho : Odd F.degree)
    (f : SL(3,F.Carrier) →* D) (hf : Function.Injective f)
    (S : Sylow 2 D) (hS : Nat.card S ≤ 128) : F.degree = 1 := by
  let U := Matrix.PSL3.LinearThree.unipotentSL F.Carrier
  have hc : Nat.card U = 2 ^ (F.degree * 3) := by
    rw [Matrix.PSL3.LinearThree.card_unipotentSL, F.card_eq, pow_mul]
  have hp : IsPGroup 2 U := IsPGroup.of_card hc
  obtain ⟨P, hP⟩ := (hp.map f).exists_le_sylow
  have hb : Nat.card (U.map f) ≤ 128 :=
    (card_le_of_le hP).trans ((Nat.card_congr (P.equiv S).toEquiv).le.trans hS)
  rw [card_map_of_injective hf, hc] at hb
  have hpow : 2 ^ (F.degree * 3) ≤ 2 ^ 7 := by norm_num at hb ⊢; exact hb
  have hn : F.degree * 3 ≤ 7 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  obtain ⟨k, hk⟩ := ho
  have hd := F.degree_pos
  omega

/-- Change the actual binary degree-one field to F₂, preserving the given
SL₃ identification. The ambient order bound alone is not a recognition premise. -/
theorem linearThree_binary_equiv (A : Subgroup D) (F : BinaryField) (ho : Odd F.degree)
    (e : A ≃* SL(3,F.Carrier)) (S : Sylow 2 D) (hS : Nat.card S ≤ 128) :
    Nonempty (A ≃* SL(3,ZMod 2)) := by
  have hn := linearThree_degree_eq_one F ho (A.subtype.comp e.symm.toMonoidHom)
    (A.subtype_injective.comp e.symm.injective) S hS
  let : Fintype F.Carrier := Fintype.ofFinite _
  let a : F.Carrier ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, F.card_eq, hn]
    simp)
  exact ⟨e.trans (Atlas.fieldEquivSL 3 a)⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
