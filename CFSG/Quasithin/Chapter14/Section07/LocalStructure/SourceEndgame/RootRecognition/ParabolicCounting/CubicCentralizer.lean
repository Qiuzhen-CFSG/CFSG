module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting.ModelCounts
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# Cubic centralizers in the literal SL₂(4) model

A diagonal cubic has exponent-three centralizer, by a finite matrix
calculation over the four-element field. Sylow conjugacy transports this
to every subgroup of order three. This excludes any nontrivial two-subgroup
from that centralizer and places the original C_S(B) in ker(qK).

Source: the quotient calculation in Aschbacher–Smith 14.7.73,
printed pp.1076–1077, manuscript of 1 March 2004.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting
open SL2FourNatural
private def cubicMatrix : SL := ⟨!![⟨0,1⟩,0;0,⟨1,1⟩], by decide⟩
private theorem cubicMatrix_order : orderOf cubicMatrix = 3 :=
  orderOf_eq_prime (by decide : cubicMatrix ^ 3 = 1) (by decide : cubicMatrix ≠ 1)
private theorem cubicCentralizer_test : ∀ x : SL,
    x * cubicMatrix = cubicMatrix * x → x ^ 3 = 1 := by decide +kernel
private theorem conjugate_commutes {A : Type*} [Group A] (g c x : A)
    (h : (g * c * g⁻¹) * x = x * (g * c * g⁻¹)) :
    (g⁻¹ * x * g) * c = c * (g⁻¹ * x * g) := by
  have hh := congrArg (fun y => g⁻¹ * y * g) h
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh.symm

/-- The literal centralizer of any cubic subgroup of SL₂(4) has exponent three. -/
theorem cubic_centralizer_cube (X : Subgroup SL) (hX : Nat.card X = 3)
    (x : SL) (hx : x ∈ centralizer (X : Set SL)) : x ^ 3 = 1 := by
  have hSL : Nat.card SL = 60 := by
    rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,
      Nat.card_eq_fintype_card, card_field]
    norm_num
  have hc : Nat.card (zpowers cubicMatrix) = 3 := by
    rw [Nat.card_zpowers, cubicMatrix_order]
  let syl (J : Subgroup SL) (hJ : Nat.card J = 3) : Sylow 3 SL :=
    (IsPGroup.of_card (n := 1) (by simpa using hJ)).toSylow (by
      have hi := J.card_mul_index
      rw [hJ, hSL] at hi
      have hind : J.index = 20 := by omega
      rw [hind]
      decide)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL (syl (zpowers cubicMatrix) hc) (syl X hX)
  have he : (zpowers cubicMatrix).map (MulAut.conj g).toMonoidHom = X :=
    congrArg (fun T : Sylow 3 SL => (T : Subgroup SL)) hg
  have hcX : g * cubicMatrix * g⁻¹ ∈ X := by
    rw [← he]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (mem_zpowers cubicMatrix)
  have hcomm := mem_centralizer_iff.mp hx _ hcX
  have hcomm' := conjugate_commutes g cubicMatrix x hcomm
  have hh := cubicCentralizer_test (g⁻¹ * x * g) hcomm'
  have hpow : (MulAut.conj g⁻¹ x) ^ 3 = 1 := by simpa only [MulAut.conj_apply, inv_inv] using hh
  rw [← map_pow, ← (MulAut.conj g⁻¹).map_one] at hpow
  exact (MulAut.conj g⁻¹).injective hpow

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting
