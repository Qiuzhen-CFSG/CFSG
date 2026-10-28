module

public import Theory.SpecificGroups.Frobenius21.Model
public import Mathlib.GroupTheory.Sylow

/-!
# Recognition and normal generation for the Frobenius group of order 21

A group of order 21 has a unique Sylow seven-subgroup, complemented by any
Sylow three-subgroup. After identifying the two cyclic factors with the
published model's kernel and complement, the complement generator acts by
one of the scalars 1, 2, or 4 on F₇. Noncommutativity excludes 1, and
inverting the complement generator changes 4 to 2. This gives an actual
multiplicative equivalence with `Frobenius21.Model`.

Every subgroup of order three normally generates the model. We verify a
finite word decomposition: a nonidentity element of order three together
with its commutator with the fixed kernel generator generates all 21 elements.
All finite calculations are checked by the Lean kernel.

These are the model facts used in Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined manuscript (1 March 2004), E.6.24–25, printed
p.255 (PDF p.266). The binary overgroup argument is in `BinaryOvergroups`.
-/

public section

open Subgroup
namespace Frobenius21
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The Sylow seven-subgroup of a group of order 21 is normal. -/
theorem normal_sylow_seven {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 21)
    (P : Sylow 7 G) : P.Normal := by
  have hp : Nat.card P = 7 := by rw [P.card_eq_multiplicity, hG]; decide +kernel
  have hi : P.index = 3 := by
    have h := P.toSubgroup.card_mul_index
    rw [hp, hG] at h
    omega
  have hd := P.card_dvd_index
  rw [hi] at hd
  have hm : Nat.card (Sylow 7 G) % 7 = 1 := card_sylow_modEq_one 7 G
  have hb := Nat.le_of_dvd (by decide : 0 < 3) hd
  have hc : Nat.card (Sylow 7 G) = 1 := by omega
  have : Subsingleton (Sylow 7 G) := (Nat.card_eq_one_iff_unique.mp hc).1
  exact P.normal_of_subsingleton

private theorem kernel_gen (x : Kernel) :
    x = (Multiplicative.ofAdd (1 : ZMod 7)) ^ x.toAdd.val := by
  change x.toAdd = x.toAdd.val • (1 : ZMod 7)
  simp

private theorem aut_formula (a : MulAut Kernel) (x : Kernel) :
    a x = Multiplicative.ofAdd ((a (Multiplicative.ofAdd 1)).toAdd * x.toAdd) := by
  conv_lhs => rw [kernel_gen x, map_pow]
  change x.toAdd.val • (a (Multiplicative.ofAdd 1)).toAdd =
    (a (Multiplicative.ofAdd 1)).toAdd * x.toAdd
  simp [mul_comm]

private theorem complement_gen (x : Complement) :
    x = (Multiplicative.ofAdd (1 : ZMod 3)) ^ x.toAdd.val := by
  change x.toAdd = x.toAdd.val • (1 : ZMod 3)
  simp

private theorem aut_pow_formula (a : MulAut Kernel) (n : ℕ) (x : Kernel) :
    (a ^ n) x = Multiplicative.ofAdd
      ((a (Multiplicative.ofAdd 1)).toAdd ^ n * x.toAdd) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, aut_formula]
    simp [pow_succ', mul_assoc]

private theorem action_formula (φ : Complement →* MulAut Kernel) (c : Complement) (x : Kernel) :
    φ c x = Multiplicative.ofAdd
      ((φ (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1)).toAdd ^ c.toAdd.val * x.toAdd) := by
  conv_lhs => rw [complement_gen c, map_pow]
  exact aut_pow_formula _ _ _

private theorem scalar_cube (φ : Complement →* MulAut Kernel) :
    (φ (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1)).toAdd ^ 3 = 1 := by
  have hp : (Multiplicative.ofAdd (1 : ZMod 3)) ^ 3 = 1 := by decide +kernel
  have hh : φ (Multiplicative.ofAdd 1) ^ 3 = 1 := by rw [← map_pow, hp, map_one]
  have h := congrArg (fun a : MulAut Kernel => a (Multiplicative.ofAdd 1)) hh
  rw [aut_pow_formula] at h
  simpa using congrArg Multiplicative.toAdd h

private theorem scalar_cases : ∀ a : ZMod 7, a ^ 3 = 1 → a = 1 ∨ a = 2 ∨ a = 4 := by
  decide +kernel

private theorem semidirect_recognition (φ : Complement →* MulAut Kernel)
    (hn : ¬ ∀ x y : SemidirectProduct Kernel Complement φ, x * y = y * x) :
    Nonempty (SemidirectProduct Kernel Complement φ ≃* Model) := by
  obtain h | h | h := scalar_cases _ (scalar_cube φ)
  · exfalso
    apply hn
    intro x y
    apply SemidirectProduct.ext
    · change x.left * φ x.right y.left = y.left * φ y.right x.left
      rw [action_formula φ x.right y.left, action_formula φ y.right x.left, h]
      simp only [one_pow, one_mul]
      exact mul_comm _ _
    · exact mul_comm _ _
  · refine ⟨SemidirectProduct.congr (MulEquiv.refl _) (MulEquiv.refl _) ?_⟩
    intro c
    apply MulEquiv.ext
    intro x
    change φ c x = action c x
    rw [action_formula, h]
    rfl
  · refine ⟨SemidirectProduct.congr (MulEquiv.refl _) (MulEquiv.inv _) ?_⟩
    intro c
    apply MulEquiv.ext
    intro x
    change φ c x = action c⁻¹ x
    rw [action_formula, h]
    exact (by decide +kernel : ∀ (c : Complement) (x : Kernel),
      Multiplicative.ofAdd ((4 : ZMod 7) ^ c.toAdd.val * x.toAdd) = action c⁻¹ x) c x

/-- Every finite nonabelian group of order 21 is isomorphic to the fixed model. -/
theorem nonempty_mulEquiv_of_card_eq {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 21)
    (hn : ¬ ∀ x y : G, x * y = y * x) : Nonempty (G ≃* Model) := by
  let P : Sylow 7 G := Classical.choice inferInstance
  let Q : Sylow 3 G := Classical.choice inferInstance
  have hp : Nat.card P = 7 := by rw [P.card_eq_multiplicity, hG]; decide +kernel
  have hq : Nat.card Q = 3 := by rw [Q.card_eq_multiplicity, hG]; decide +kernel
  have : P.Normal := normal_sylow_seven hG P
  have hcomp : P.toSubgroup.IsComplement' Q.toSubgroup :=
    isComplement'_of_coprime (by rw [hp, hq, hG]) (by rw [hp, hq]; decide)
  let e := SemidirectProduct.mulEquivSubgroup hcomp
  let ep : P ≃* Kernel := mulEquivOfPrimeCardEq hp (Nat.card_zmod 7)
  let eq : Q ≃* Complement := mulEquivOfPrimeCardEq hq (Nat.card_zmod 3)
  let e' := SemidirectProduct.congr' (φ₁ := (P.toSubgroup.normalizerMonoidHom).comp
    (inclusion (P.toSubgroup.normalizer_eq_top ▸ le_top))) ep eq
  let d := e.symm.trans e'
  obtain ⟨f⟩ := semidirect_recognition _ (by
    intro hc
    apply hn
    intro x y
    apply d.injective
    simpa only [map_mul] using hc (d x) (d y))
  exact ⟨e.symm.trans (e'.trans f)⟩

private def kernelGenerator : Model := SemidirectProduct.inl (Multiplicative.ofAdd 1)

set_option maxRecDepth 2048 in
private theorem normal_words : ∀ x : Model, x ^ 3 = 1 → x ≠ 1 →
    ∀ z : Model, ∃ i : Fin 3, ∃ j : Fin 7,
    z = x ^ i.val * (kernelGenerator * x * kernelGenerator⁻¹ * x⁻¹) ^ j.val := by
  decide +kernel

/-- Every subgroup of order three normally generates the whole model. -/
theorem normalClosure_eq_top_of_card_three (C : Subgroup Model) (hC : Nat.card C = 3) :
    normalClosure (C : Set Model) = ⊤ := by
  have : Nontrivial C := C.nontrivial_iff_ne_bot.mpr
    (C.one_lt_card_iff_ne_bot.mp (by omega))
  obtain ⟨x, hx, hx1⟩ := C.exists_ne_one_of_nontrivial
  have hx3 : x ^ 3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨x, hx⟩ : C))
    rw [hC] at hh
    exact congrArg Subtype.val hh
  apply top_unique
  intro z _
  obtain ⟨i, j, rfl⟩ := normal_words x hx3 hx1 z
  apply Subgroup.mul_mem
  · exact Subgroup.pow_mem _ (subset_normalClosure hx) _
  · apply Subgroup.pow_mem
    apply Subgroup.mul_mem
    · exact Subgroup.Normal.conj_mem inferInstance x (subset_normalClosure hx) kernelGenerator
    · exact Subgroup.inv_mem _ (subset_normalClosure hx)

end Frobenius21
