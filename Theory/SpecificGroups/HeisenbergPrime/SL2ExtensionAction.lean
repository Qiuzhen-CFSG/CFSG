module

public import Theory.SpecificGroups.HeisenbergPrime
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.SpecificGroups.SL2.PrimePlaneAction
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.OddKernelInvolutionFibers
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The nontrivial SL₂ quotient action of a Heisenberg extension

If P is a normal prime Heisenberg group in L and L/P is SL₂(p), p > 3,
a nontrivial action on P/Z(P) is faithful modulo P. The central involution
of SL₂(p) inverts this plane and lifts to an involution t in L. Conjugacy
of involutions through an odd kernel makes C_L(t) cover L/P. Its intersection
with P lies in Z(P), which is centralized by L because SL₂(p) is perfect
and the automorphism group of the cyclic center is abelian.

All actions and projections below are the literal normal-subgroup conjugation
and quotient maps. Source: Aschbacher--Smith, A.1.33(2), printed p.29.
-/

open Subgroup
open scoped IsMulCommutative MatrixGroups

namespace HeisenbergPrime.SL2ExtensionAction

variable {L : Type*} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]

omit [Finite L] in
private theorem center_fixed (P : Subgroup L) [P.Normal]
    (eP : P ≃* HeisenbergPrime p) (hp : 3 < p)
    (eQ : L ⧸ P ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (x : L) (z : center P) : MulAut.conjNormal x (z : P) = z := by
  have hc : Nat.card (center P) = p :=
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
  let d := (IsCyclic.mulAutMulEquiv (center P)).toMonoidHom.comp
    ((QuotientGroup.lift P r hr).comp eQ.symm.toMonoidHom)
  let := Matrix.SpecialLinearGroup.PrimePlaneAction.perfect hp
  have hd : d = 1 := by
    apply MonoidHom.ker_eq_top_iff.mp
    apply top_unique
    rw [← Group.IsPerfect.commutator_eq_top (G := Matrix.SpecialLinearGroup (Fin 2) (ZMod p))]
    exact Abelianization.commutator_subset_ker d
  have hh := DFunLike.congr_fun hd (eQ (QuotientGroup.mk' P x))
  have hrx : r x = 1 := by
    apply (IsCyclic.mulAutMulEquiv (center P)).injective
    simpa [d] using hh
  exact congrArg Subtype.val (DFunLike.congr_fun hrx z)

private theorem centralizer_surjective (P : Subgroup L) [P.Normal]
    (hodd : Odd (Nat.card P)) (t : L) (ht : orderOf t = 2)
    (hz : QuotientGroup.mk' P t ∈ center (L ⧸ P)) :
    Function.Surjective ((QuotientGroup.mk' P).comp (centralizer ({t} : Set L)).subtype) := by
  let q := QuotientGroup.mk' P
  have hk : Nat.Coprime 2 (Nat.card q.ker) := by
    simpa only [q, QuotientGroup.ker_mk'] using Nat.coprime_two_left.mpr hodd
  intro v
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective P v
  have hxord : orderOf (MulAut.conj x t) = 2 := ((MulAut.conj x).orderOf_eq t).trans ht
  have hxq : q (MulAut.conj x t) = q t := by
    change q (x * t * x⁻¹) = q t
    rw [map_mul, map_mul, map_inv, Subgroup.mem_center_iff.mp hz (q x), mul_inv_cancel_right]
  obtain ⟨g, hg⟩ := involutions_same_image_conj_ker q hk hxord ht hxq
  have hct : (g : L) * x ∈ centralizer ({t} : Set L) := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    simpa only [MulAut.conj_apply, mul_inv_rev, mul_assoc] using hg
  refine ⟨⟨(g : L) * x, hct⟩, ?_⟩
  change q ((g : L) * x) = q x
  rw [map_mul, g.property, one_mul]

/-- A nontrivial quotient action produces the inverter and its centralizer
geometry, with no faithfulness or splitting assumptions. -/
public theorem exists_involution_centralizer
    (P : Subgroup L) [P.Normal] (eP : P ≃* HeisenbergPrime p) (hp : 3 < p)
    (eQ : L ⧸ P ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hne : ∃ x : L, quotientAut (center P) (MulAut.conjNormal x) ≠ 1) :
    ∃ t : L, orderOf t = 2 ∧
      (∀ v : P ⧸ center P, quotientAut (center P) (MulAut.conjNormal t) v = v⁻¹) ∧
      Function.Surjective ((QuotientGroup.mk' P).comp (centralizer ({t} : Set L)).subtype) ∧
      (∀ c : centralizer ({t} : Set L), (c : L) ∈ P →
        c ∈ center (centralizer ({t} : Set L))) ∧
      (∀ x : L, x ∉ P → quotientAut (center P) (MulAut.conjNormal x) ≠ 1) := by
  let : IsExtraspecial p P :=
    (HeisenbergPrime.isExtraspecial (by omega : p ≠ 2)).of_mulEquiv eP.symm
  let : IsElementaryAbelian p (P ⧸ center P) := IsExtraspecial.quotient_elementary_abelian p P
  let a : L →* MulAut (P ⧸ center P) := (quotientAut (center P)).comp MulAut.conjNormal
  have haP : P ≤ a.ker := by
    intro x hx
    change MulAut.conjNormal x ∈ (quotientAut (center P)).ker
    rw [IsExtraspecial.quotientAut_center_ker_eq_range_conj (p := p)]
    exact ⟨⟨x, hx⟩, (MulAut.conjNormal_val (h := (⟨x, hx⟩ : P))).symm⟩
  let ρ := (QuotientGroup.lift P a haP).comp eQ.symm.toMonoidHom
  have hρx (x : L) : ρ (eQ (QuotientGroup.mk' P x)) = a x := by simp [ρ]
  have hρ : ρ ≠ 1 := by
    intro h
    obtain ⟨x, hx⟩ := hne
    apply hx
    have hh := hρx x
    rw [h] at hh
    exact hh.symm
  have hZ : Nat.card (center P) = p :=
    (Nat.card_congr (centerCongr eP).toEquiv).trans HeisenbergPrime.card_center
  have hV : Nat.card (P ⧸ center P) = p ^ 2 := by
    have h := (center P).card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr eP.toEquiv, HeisenbergPrime.card, hZ, pow_succ] at h
    exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos h.symm
  obtain ⟨hfaith, hinv⟩ := Matrix.SpecialLinearGroup.PrimePlaneAction.faithful_and_inverts hp hV ρ hρ
  have hpow (y : P) : y ^ p = 1 := by
    apply eP.injective
    rw [map_pow, HeisenbergPrime.pow_prime (by omega : p ≠ 2), map_one]
  let f := eQ.toMonoidHom.comp (QuotientGroup.mk' P)
  have hf : Function.Surjective f := eQ.surjective.comp (QuotientGroup.mk'_surjective P)
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨x, hx⟩ := hf (-1)
  have hx2 : x ^ 2 ∈ P := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply eQ.injective
    change f (x ^ 2) = eQ 1
    rw [map_pow, hx, map_one]
    norm_num
  let t := x ^ p
  have ht2 : t ^ 2 = 1 := by
    have hh := congrArg Subtype.val (hpow ⟨x ^ 2, hx2⟩)
    change (x ^ 2) ^ p = 1 at hh
    change t ^ 2 = 1
    simpa only [t, ← pow_mul, Nat.mul_comm] using hh
  have hft : f t = -1 := by
    change f (x ^ p) = -1
    rw [map_pow, hx, hpodd.neg_one_pow]
  have hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) ≠ 1 := by
    intro h
    have hh := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) => A 0 0) h
    have hh' : (-1 : ZMod p) = 1 := by simpa using hh
    have h2 : (2 : ZMod p) = 0 := by linear_combination -hh'
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p)
      ((ZMod.natCast_eq_zero_iff 2 p).mp h2)
  have ht : orderOf t = 2 := by
    apply orderOf_eq_prime_iff.mpr
    refine ⟨ht2, ?_⟩
    intro ht1
    exact hneg (hft.symm.trans (by simp [ht1]))
  have hti : ∀ v : P ⧸ center P, quotientAut (center P) (MulAut.conjNormal t) v = v⁻¹ := by
    intro v
    have hh := hρx t
    change ρ (f t) = a t at hh
    rw [hft] at hh
    exact (congrArg (fun b : MulAut (P ⧸ center P) => b v) hh).symm.trans (hinv v)
  refine ⟨t, ht, hti, centralizer_surjective P ?_ t ht ?_, ?_, ?_⟩
  · rw [Nat.card_congr eP.toEquiv, HeisenbergPrime.card]
    exact hpodd.pow
  · apply Subgroup.mem_center_iff.mpr
    intro v
    apply eQ.injective
    rw [map_mul, map_mul]
    change eQ v * f t = f t * eQ v
    rw [hft]
    simp
  · intro c hc
    let y : P := ⟨c, hc⟩
    have hyfix : MulAut.conjNormal t y = y := by
      apply Subtype.ext
      change t * (c : L) * t⁻¹ = c
      rw [(mem_centralizer_singleton_iff.mp c.property).symm, mul_inv_cancel_right]
    have hqy : QuotientGroup.mk' (center P) y = (QuotientGroup.mk' (center P) y)⁻¹ := by
      simpa only [quotientAut_apply_mk, hyfix] using hti (QuotientGroup.mk' (center P) y)
    have hq2 : (QuotientGroup.mk' (center P) y) ^ 2 = 1 := by
      simpa only [pow_two] using (eq_inv_iff_mul_eq_one.mp hqy)
    have hqp : (QuotientGroup.mk' (center P) y) ^ p = 1 := by
      rw [← map_pow, hpow, map_one]
    have hyZ : y ∈ center P := (QuotientGroup.eq_one_iff y).mp
      ((pow_eq_one_iff_of_coprime (Nat.coprime_two_left.mpr hpodd)).mp ⟨hq2, hqp⟩)
    apply Subgroup.mem_center_iff.mpr
    intro b
    apply Subtype.ext
    have hh := congrArg Subtype.val (center_fixed P eP hp eQ (b : L) ⟨y, hyZ⟩)
    change (b : L) * (c : L) * (b : L)⁻¹ = c at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · intro y hy hya
    apply hy
    apply (QuotientGroup.eq_one_iff y).mp
    apply eQ.injective
    apply hfaith
    change ρ (eQ (QuotientGroup.mk' P y)) = ρ (eQ 1)
    rw [hρx, map_one, map_one]
    exact hya

end HeisenbergPrime.SL2ExtensionAction
