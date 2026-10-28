module

public import Theory.SpecificGroups.HeisenbergPrime
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupAction.Extraspecial27InvolutionFixed
public import Theory.SpecificGroups.SL2.NormalMonolith
public import Theory.SpecificGroups.SL2.NoIndexTwo
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Involutions in extensions of the group of order 27 by SL₂(3)

Let P be a normal subgroup of a finite group L, with P isomorphic to the
prime Heisenberg group of order 27 and L/P isomorphic to SL₂(3). An involution
t acting nontrivially on P inverts P/Z(P). Moreover Z(L) has order three,
and the kernel of the action of C_L(t) on P/Z(P) is Z(L).

SL₂(3) has no quotient of order two, so L fixes the cyclic center of P.
The fixed subgroup of its nontrivial involutory automorphism is then Z(P).
The fixed/inverted factorization gives inversion on the central quotient.
The inner-automorphism kernel has exponent three, so t remains nontrivial
on that quotient. Its image in SL₂(3) is -1; every nontrivial normal subgroup
of SL₂(3) contains -1, making the quotient action faithful modulo P.
Consequently the center of L is exactly the embedded center of P, and the
fixed-subgroup identity also identifies the centralizer's action kernel.

These are the action and center calculations used in Aschbacher--Smith,
*The Classification of Quasithin Groups*, A.1.33(3), printed p.29.
The action throughout is the literal normal-subgroup conjugation followed
by `Subgroup.quotientAut`, with no assumed nontriviality on P/Z(P).
-/

open Subgroup
open scoped IsMulCommutative MatrixGroups
namespace HeisenbergPrime.SL23InvolutionAction
variable {L : Type*} [Group L] [Finite L]

private theorem hom_eq_one_of_card_two {A : Type*} [Group A] [Finite A]
    (hA : Nat.card A = 2)
    (f : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) →* A) : f = 1 := by
  have hd : Nat.card f.range ∣ 2 := by simpa only [hA] using f.range.card_subgroup_dvd_card
  have hcard : Nat.card f.range = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact h
    · exact (Matrix.SpecialLinearGroup.index_ne_two (by decide : (2 : ZMod 3) ≠ 0)
        f.ker ((Subgroup.index_ker f).trans h)).elim
  exact MonoidHom.range_eq_bot_iff.mp (Subgroup.card_eq_one.mp hcard)

private theorem center_fixed (P : Subgroup L) [P.Normal]
    (eP : P ≃* HeisenbergPrime 3)
    (eQ : L ⧸ P ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (x : L) (z : center P) : MulAut.conjNormal x (z : P) = z := by
  have hc : Nat.card (center P) = 3 :=
    (Nat.card_congr (centerCongr eP).toEquiv).trans HeisenbergPrime.card_center
  let : IsCyclic (center P) := isCyclic_of_prime_card hc
  let r : L →* MulAut (center P) :=
    (MulAut.characteristic (center P)).comp MulAut.conjNormal
  have hr : P ≤ r.ker := by
    intro y hy
    change MulAut.characteristic (center P) (MulAut.conjNormal y) = 1
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    change MulAut.conjNormal y (w : P) = w
    rw [MulAut.conjNormal_val (h := (⟨y, hy⟩ : P)), MulAut.conj_apply]
    rw [(Subgroup.mem_center_iff.mp w.property ⟨y, hy⟩), mul_inv_cancel_right]
  let d := (QuotientGroup.lift P r hr).comp eQ.symm.toMonoidHom
  have hd : d = 1 := hom_eq_one_of_card_two (by rw [IsCyclic.card_mulAut, hc]; decide) d
  have hrx : r x = 1 := by
    have hh := DFunLike.congr_fun hd (eQ (QuotientGroup.mk' P x))
    simpa [d] using hh
  exact congrArg Subtype.val (DFunLike.congr_fun hrx z)

private theorem sl23_involution {g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)}
    (hg : g ^ 2 = 1) (hne : g ≠ 1) : g = -1 := by
  have h := Matrix.GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one
    (by decide : (2 : ZMod 3) ≠ 0) (Matrix.SpecialLinearGroup.toGL g)
    (by rw [← map_pow, hg, map_one]) (by apply Units.ext; exact g.property)
  rcases h with h | h
  · exact (hne (Matrix.SpecialLinearGroup.toGL_injective (by simpa using h))).elim
  · apply Subtype.ext
    exact congrArg Units.val h

/-- An involution nontrivial on P inverts P/Z(P); the ambient center has
order three and contains every element of C_L(t) acting trivially on P/Z(P).
Thus an order-three subgroup of C_L(t) distinct from Z(L) supplies a
nontrivial quotient actor, as required by A.1.33(1). -/
public theorem involution_action_and_center
    (P : Subgroup L) [P.Normal] (eP : P ≃* HeisenbergPrime 3)
    (eQ : L ⧸ P ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (t : L) (ht : orderOf t = 2) (hne : (MulAut.conjNormal t : MulAut P) ≠ 1) :
    (∀ v : P ⧸ center P, quotientAut (center P) (MulAut.conjNormal t) v = v⁻¹) ∧
    Nat.card (center L) = 3 ∧
    (∀ x ∈ centralizer ({t} : Set L),
      quotientAut (center P) (MulAut.conjNormal x) = 1 → x ∈ center L) := by
  let : IsExtraspecial 3 P :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv eP.symm
  have hPcard : Nat.card P = 27 := by
    rw [Nat.card_congr eP.toEquiv, HeisenbergPrime.card]
    norm_num
  have hpow (y : P) : y ^ 3 = 1 := by
    apply eP.injective
    rw [map_pow, HeisenbergPrime.pow_prime (by decide : 3 ≠ 2), map_one]
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have hat2 : (MulAut.conjNormal t : MulAut P) ^ 2 = 1 := by
    rw [← map_pow, ht2, map_one]
  have hai : Function.Involutive (MulAut.conjNormal t : MulAut P) := by
    intro y
    exact DFunLike.congr_fun hat2 y
  have hfixed : (MulAut.conjNormal t : MulAut P).fixedSubgroup = center P :=
    MulAut.fixed_eq_center_of_extraspecial27_involution hPcard _ hai hne
      (fun z hz => center_fixed P eP eQ t ⟨z, hz⟩)
  have hinv : ∀ v : P ⧸ center P,
      quotientAut (center P) (MulAut.conjNormal t) v = v⁻¹ := by
    intro v
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center P) v
    obtain ⟨⟨u, w⟩, ⟨hu, hw, huw⟩, _⟩ :=
      Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card
        (by rw [hPcard]; decide) (MulAut.conjNormal t) hai y
    have hqu : QuotientGroup.mk' (center P) u = 1 :=
      (QuotientGroup.eq_one_iff u).mpr (hfixed ▸ (MulAut.mem_fixedSubgroup _ _).mpr hu)
    rw [quotientAut_apply_mk, ← huw, map_mul, hu, hw, map_mul, map_inv, hqu,
      one_mul, map_mul, hqu, one_mul]
  let a : L →* MulAut (P ⧸ center P) := (quotientAut (center P)).comp MulAut.conjNormal
  have haP : P ≤ a.ker := by
    intro x hx
    change MulAut.conjNormal x ∈ (quotientAut (center P)).ker
    rw [IsExtraspecial.quotientAut_center_ker_eq_range_conj (p := 3)]
    exact ⟨⟨x, hx⟩, (MulAut.conjNormal_val (h := (⟨x, hx⟩ : P))).symm⟩
  have hat : a t ≠ 1 := by
    intro h
    have hk : MulAut.conjNormal t ∈ (quotientAut (center P)).ker := h
    rw [IsExtraspecial.quotientAut_center_ker_eq_range_conj (p := 3)] at hk
    obtain ⟨y, hy⟩ := hk
    have hat3 : (MulAut.conjNormal t : MulAut P) ^ 3 = 1 := by
      rw [← hy, ← map_pow, hpow, map_one]
    exact hne ((pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 2 3)).mp ⟨hat2, hat3⟩)
  let ρ := (QuotientGroup.lift P a haP).comp eQ.symm.toMonoidHom
  have hρx (x : L) : ρ (eQ (QuotientGroup.mk' P x)) = a x := by simp [ρ]
  have hqt : eQ (QuotientGroup.mk' P t) = -1 := by
    apply sl23_involution
    · rw [← map_pow, ← map_pow, ht2, map_one, map_one]
    · intro h
      apply hat
      rw [← hρx, h, map_one]
  have hfaith : Function.Injective ρ := by
    apply (MonoidHom.ker_eq_bot_iff ρ).mp
    apply Matrix.SpecialLinearGroup.eq_bot_of_neg_one_not_mem
      (by decide : (2 : ZMod 3) ≠ 0)
    intro h
    apply hat
    rw [← hρx, hqt]
    exact h
  have hkernel (x : L) (hx : a x = 1) : x ∈ P := by
    apply (QuotientGroup.eq_one_iff x).mp
    apply eQ.injective
    apply hfaith
    change ρ (eQ (QuotientGroup.mk' P x)) = ρ (eQ 1)
    rw [hρx, map_one, map_one]
    exact hx
  have hcentral (z : center P) : ((z : P) : L) ∈ center L := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    have hh := congrArg Subtype.val (center_fixed P eP eQ x z)
    change x * ((z : P) : L) * x⁻¹ = ((z : P) : L) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hZeq : center L = (center P).map P.subtype := by
    apply le_antisymm
    · intro x hx
      have hc : (MulAut.conjNormal x : MulAut P) = 1 := by
        apply MulEquiv.ext
        intro y
        apply Subtype.ext
        change x * (y : L) * x⁻¹ = y
        rw [← Subgroup.mem_center_iff.mp hx (y : L), mul_inv_cancel_right]
      have hxP : x ∈ P := hkernel x (by change quotientAut (center P) _ = 1; rw [hc, map_one])
      refine ⟨⟨x, hxP⟩, ?_, rfl⟩
      apply Subgroup.mem_center_iff.mpr
      intro y
      exact Subtype.ext (Subgroup.mem_center_iff.mp hx (y : L))
    · rintro x ⟨z, hz, rfl⟩
      exact hcentral ⟨z, hz⟩
  refine ⟨hinv, ?_, ?_⟩
  · rw [hZeq]
    exact (Nat.card_congr ((center P).equivMapOfInjective P.subtype
      P.subtype_injective).toEquiv).symm.trans
        ((Nat.card_congr (centerCongr eP).toEquiv).trans HeisenbergPrime.card_center)
  · intro x hxt hxa
    have hxP : x ∈ P := hkernel x hxa
    let y : P := ⟨x, hxP⟩
    have hy : MulAut.conjNormal t y = y := by
      apply Subtype.ext
      change t * x * t⁻¹ = x
      rw [← mem_centralizer_singleton_iff.mp hxt, mul_inv_cancel_right]
    exact hcentral ⟨y, hfixed ▸ (MulAut.mem_fixedSubgroup _ _).mpr hy⟩

end HeisenbergPrime.SL23InvolutionAction
