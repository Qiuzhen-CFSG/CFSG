module
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual
public import Theory.GroupTheory.CyclicTwoAut
public import Theory.GroupTheory.PResidual.OddCoreSupplement
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupAction.Invariant
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
# Irreducibility of the original two-core in degree two

A determinant-one two-group preserving a line in characteristic three or
five embeds in that line's cyclic automorphism group. The kernel fixes a
nonzero vector, so its matrices are unipotent of odd prime order and hence
trivial. A cyclic normal two-group has a two-group of automorphisms.
Two-perfectness centralizes it, and the cubic quotient then makes the
whole image abelian, forcing its two-core image to vanish.

Source application: the actual prime-five and ternary Frattini actions in
Aschbacher--Smith 15.4.10, printed p.1159.
-/

public section
open Subgroup Matrix
open scoped IsMulCommutative
namespace Matrix.GeneralLinearGroup.PrimeThreeFiveResidual
variable {X H : Type*} [Group X] [Finite X] [Group H]

/-- A cyclic two-core image is trivial for an original cubic two-residual. -/
theorem core_image_eq_bot_of_cyclic (hX : IsPPerfect 2 X)
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3) (f : X →* H)
    [IsCyclic ((pCore 2 X).map f)] : (pCore 2 X).map f = ⊥ := by
  let K := f.range
  let : Finite K := Finite.of_surjective _ f.rangeRestrict_surjective
  let R := (pCore 2 X).map f.rangeRestrict
  let : R.Normal := (pCore_normal (p := 2) (G := X)).map _ f.rangeRestrict_surjective
  have hRtwo : IsPGroup 2 R := pCore_isPGroup.map f.rangeRestrict
  let r : R →* (pCore 2 X).map f :=
    (K.subtype.comp R.subtype).codRestrict _ (by
      rintro ⟨r, x, hx, rfl⟩
      exact mem_map_of_mem f hx)
  let : IsCyclic R := isCyclic_of_injective r (by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : (pCore 2 X).map f => (z : H)) h)))
  have hpK : IsPPerfect 2 K := hX.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hf : (MulAut.conjNormal : K →* MulAut R) = 1 :=
    hpK.hom_eq_one_of_isPGroup hRtwo.mulAut_of_isCyclic_two _
  have hRZ : R ≤ center K := by
    intro r hr
    apply mem_center_iff.mpr
    intro k
    have hh := congrArg (fun a : MulAut R => (a ⟨r, hr⟩ : K)) (DFunLike.congr_fun hf k)
    change k * r * k⁻¹ = r at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  let q := QuotientGroup.mk' R
  let u := q.comp f.rangeRestrict
  have hk : pCore 2 X ≤ u.ker := by
    intro x hx
    exact (QuotientGroup.eq_one_iff (N := R) _).mpr (mem_map_of_mem f.rangeRestrict hx)
  let v := QuotientGroup.lift (pCore 2 X) u hk
  have hv : Function.Surjective v := by
    intro y
    obtain ⟨x, rfl⟩ := (QuotientGroup.mk'_surjective R).comp f.rangeRestrict_surjective y
    exact ⟨QuotientGroup.mk' (pCore 2 X) x, rfl⟩
  let : IsCyclic (X ⧸ pCore 2 X) := isCyclic_of_prime_card hX3
  let : IsCyclic (K ⧸ R) := isCyclic_of_surjective v hv
  let : IsMulCommutative K := q.isMulCommutative_of_isCyclic_of_ker_le_center
    (by simpa only [q, QuotientGroup.ker_mk'] using hRZ)
  let : CommGroup K := IsMulCommutative.instCommGroup
  have hcop : Nat.Coprime 2 (Nat.card K) := coprime_card_of_isPPerfect_commGroup hpK
  obtain ⟨n, hn⟩ := hRtwo.exists_card_dvd_pow
  have hRcard : Nat.card R = 1 :=
    Nat.eq_one_of_dvd_coprimes (hcop.pow_left n) hn R.card_subgroup_dvd_card
  have hRb : R = ⊥ := Subgroup.card_eq_one.mp hRcard
  apply eq_bot_iff.mpr
  rintro y ⟨x, hx, rfl⟩
  have hh : f.rangeRestrict x = 1 := mem_bot.mp (hRb ▸ mem_map_of_mem f.rangeRestrict hx)
  exact congrArg (fun k : K => (k : H)) hh

private theorem square_sub_one {F : Type*} [Field F]
    (A : Matrix (Fin 2) (Fin 2) F) (hd : A.det = 1) (hs : (A-1).det = 0) :
    (A-1)^2 = 0 := by
  simp [Matrix.det_fin_two] at hd hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination A 0 0 * (hd - hs) - hd
  · linear_combination A 0 1 * (hd - hs)
  · linear_combination A 1 0 * (hd - hs)
  · linear_combination A 1 1 * (hd - hs) - hd

private theorem nilpotent_add_one_pow {R : Type*} [Ring R] (N : R) (hN : N ^ 2 = 0)
    (n : ℕ) : (N+1)^n = 1 + n • N := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, succ_nsmul]
    have hNN : N*N = 0 := by simpa only [pow_two] using hN
    simp only [add_mul, one_mul, mul_one, mul_add, smul_mul_assoc, hNN, nsmul_zero]
    abel

private theorem unipotent {p : ℕ} [Fact p.Prime]
    (A : Matrix (Fin 2) (Fin 2) (ZMod p)) (hd : A.det = 1) (hs : (A-1).det = 0) :
    A ^ p = 1 := by
  have hh := nilpotent_add_one_pow (A-1) (square_sub_one A hd hs) p
  rw [sub_add_cancel] at hh
  rw [hh]
  have hz : p • (A-1) = 0 := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.zero_apply]
    simp [nsmul_eq_mul]
  rw [hz, add_zero]

/-- A determinant-one matrix fixing a nonzero vector in the two source
characteristics is unipotent of order dividing the characteristic. -/
theorem pow_eq_one_of_fixed_vector {p : ℕ} [Fact p.Prime] (_hp : p = 3 ∨ p = 5)
    (g : GL (Fin 2) (ZMod p)) (hg : g.det = 1)
    (v : Fin 2 → ZMod p) (hv : v ≠ 0) (hfix : g.val *ᵥ v = v) : g ^ p = 1 := by
  have hs : (g.val - 1).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨v, hv, by simp only [Matrix.sub_mulVec, Matrix.one_mulVec, hfix, sub_self]⟩
  have hd : g.val.det = 1 := congrArg Units.val hg
  exact Units.ext (unipotent g.val hd hs)

/-- The natural GL₂ action on the actual additive prime plane. -/
@[expose] def planeAction (p : ℕ) : GL (Fin 2) (ZMod p) →*
    MulAut (Multiplicative (Fin 2 → ZMod p)) where
  toFun g := (GeneralLinearGroup.toLin g).toLinearEquiv.toAddEquiv.toMultiplicative
  map_one' := by
    ext v : 1
    change (GeneralLinearGroup.toLin (1 : GL (Fin 2) (ZMod p)) :
      Module.End (ZMod p) (Fin 2 → ZMod p)) v.toAdd = v.toAdd
    rw [map_one]
    rfl
  map_mul' g h := by
    ext v : 1
    change (GeneralLinearGroup.toLin (g * h) : Module.End (ZMod p) (Fin 2 → ZMod p)) v.toAdd =
      (GeneralLinearGroup.toLin g : Module.End (ZMod p) (Fin 2 → ZMod p))
        ((GeneralLinearGroup.toLin h : Module.End (ZMod p) (Fin 2 → ZMod p)) v.toAdd)
    rw [map_mul]
    rfl

/-- Every invariant prime-order line detects a determinant-one two-group
faithfully, hence that two-group is cyclic. -/
theorem cyclic_of_invariant_line {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 5)
    (R : Subgroup (GL (Fin 2) (ZMod p))) (hR : IsPGroup 2 R)
    (hdet : ∀ g ∈ R, g.det = 1)
    (L : Subgroup (Multiplicative (Fin 2 → ZMod p))) (hc : Nat.card L = p)
    (hinv : ∀ g ∈ R, ∀ v ∈ L, planeAction p g v ∈ L) : IsCyclic R := by
  let a := (planeAction p).comp R.subtype
  let : MulDistribMulAction R (Multiplicative (Fin 2 → ZMod p)) :=
    MulDistribMulAction.compHom _ a
  let : IsInvariant R (Multiplicative (Fin 2 → ZMod p)) L := ⟨fun g v =>
    ⟨hinv g g.property v, fun hv => by
      have hh := hinv g⁻¹ (R.inv_mem g.property) (planeAction p g v) hv
      simpa only [map_inv, MulAut.inv_apply_self] using hh⟩⟩
  let b := MulDistribMulAction.toMulAut R L
  have hb : Function.Injective b := by
    apply (MonoidHom.ker_eq_bot_iff b).mp
    apply eq_bot_iff.mpr
    intro g hg
    let : Nontrivial L := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; exact (Fact.out : p.Prime).one_lt)
    obtain ⟨v, hv⟩ := exists_ne (1 : L)
    have hfix := congrArg (fun c : MulAut L => (c v : Multiplicative (Fin 2 → ZMod p))) hg
    have hv0 : v.val.toAdd ≠ 0 := fun he => hv (Subtype.ext he)
    have hgp : g.val ^ p = 1 := pow_eq_one_of_fixed_vector hp g (hdet g g.property) v.val.toAdd hv0 hfix
    have hg1 : g = 1 := (hR.powEquiv (by rcases hp with rfl | rfl <;> decide)).injective
      (show g ^ p = (1 : R) ^ p from (Subtype.ext hgp).trans (one_pow p).symm)
    exact hg1
  let : IsCyclic L := isCyclic_of_prime_card hc
  let : Fact (Nat.card L).Prime := ⟨by rw [hc]; exact Fact.out⟩
  let : IsCyclic (MulAut L) := isCyclic_of_injective (IsCyclic.mulAutMulEquiv L).toMonoidHom
    (IsCyclic.mulAutMulEquiv L).injective
  exact isCyclic_of_injective b hb

end Matrix.GeneralLinearGroup.PrimeThreeFiveResidual

namespace Matrix.GeneralLinearGroup.PrimeThreeFiveResidual
open Subgroup Matrix
open scoped IsMulCommutative
variable {X : Type*} [Group X] [Finite X]

private theorem plane_line_card {p : ℕ} [Fact p.Prime]
    (L : Subgroup (Multiplicative (Fin 2 → ZMod p))) (hb : L ≠ ⊥) (ht : L ≠ ⊤) :
    Nat.card L = p := by
  have hc : Nat.card (Multiplicative (Fin 2 → ZMod p)) = p ^ 2 := by
    change Nat.card (Fin 2 → ZMod p) = p ^ 2
    simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hpL : IsPGroup p L := (IsPGroup.of_card (n := 2) hc).to_subgroup L
  obtain ⟨n, hn⟩ := hpL.exists_card_eq
  have hle : n ≤ 2 := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    (by simpa only [hn, hc] using Subgroup.card_le_card_group L)
  have h0 : n ≠ 0 := by
    intro h
    exact hb (Subgroup.card_eq_one.mp (by simpa only [h, pow_zero] using hn))
  have h2 : n ≠ 2 := by
    intro h
    exact ht (L.eq_top_of_card_eq (hn.trans (h ▸ hc.symm)))
  have h1 : n = 1 := by omega
  simpa only [h1, pow_one] using hn

omit [Finite X] in
/-- Determinant is trivial in both source characteristics because the
multiplicative groups of the prime fields are two-groups. -/
theorem det_eq_one {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 5)
    (hX : IsPPerfect 2 X) (a : X →* GL (Fin 2) (ZMod p)) (x : X) : (a x).det = 1 := by
  have hU : IsPGroup 2 (ZMod p)ˣ := by
    rcases hp with rfl | rfl
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime (by decide)]; norm_num)
    · exact IsPGroup.of_card (n := 2) (by rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime (by decide)]; norm_num)
  exact DFunLike.congr_fun (hX.hom_eq_one_of_isPGroup hU (GeneralLinearGroup.det.comp a)) x

/-- The two-core itself acts irreducibly; irreducibility of the whole image
is not substituted for this stronger source conclusion. -/
theorem core_irreducible {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 5)
    (hX : IsPPerfect 2 X) (hX3 : Nat.card (X ⧸ pCore 2 X) = 3)
    (a : X →* GL (Fin 2) (ZMod p)) (hne : (pCore 2 X).map a ≠ ⊥)
    (L : Subgroup (Multiplicative (Fin 2 → ZMod p)))
    (hinv : ∀ x ∈ pCore 2 X, ∀ v ∈ L, planeAction p (a x) v ∈ L) : L = ⊥ ∨ L = ⊤ := by
  by_cases hb : L = ⊥
  · exact Or.inl hb
  by_cases ht : L = ⊤
  · exact Or.inr ht
  have hc := plane_line_card L hb ht
  let : IsCyclic ((pCore 2 X).map a) := cyclic_of_invariant_line hp _ (pCore_isPGroup.map a)
    (by rintro g ⟨x, _, rfl⟩; exact det_eq_one hp hX a x) L hc (by
      rintro g ⟨x, hx, rfl⟩ v hv
      exact hinv x hx v hv)
  exact (hne (core_image_eq_bot_of_cyclic hX hX3 a)).elim

end Matrix.GeneralLinearGroup.PrimeThreeFiveResidual
