module

public import Theory.SpecificGroups.ExoticTwoGroup.LiftCorrection
import Mathlib.Tactic

/-!
# Choosing the inversion basis in the exotic extension

If the inversion commutator with the first inner generator is outside W,
its coordinates are odd-even; those of the second commutator are even-odd.
Consequently these commutators generate the whole C₄-square base. Correcting
the inverter by either 1 or a equalizes their off-diagonal coordinates.
Taking these corrected commutators as basis gives the prescribed inversion
relations. The swap acts on the new basis either by exchange or by negative
exchange; multiplying it by the inverter removes the latter sign.

This proves the entire algebraic inversion normalization from two explicit
structural inputs: the inversion square is one and the first inversion
commutator lies outside W. Neither structural input is assumed as an axiom.

Source: MacWilliams, Trans. AMS 150 (1970), (xii) and (xviii), pp.392–396;
Janko–Thompson, Math. Z. 113 (1970), 1.4(c), printed p.386.
-/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 2048
open Subgroup
namespace ExoticTwoGroup.ActionFrame
variable {P : Type*} [Group P] {D W B : Subgroup P}
variable (f : ActionFrame D W B)
private def word (i j : ZMod 4) : P := f.a ^ i.val * f.b ^ j.val
private theorem word_zero : f.word 0 0 = 1 := by norm_num [word]
private theorem word_a : f.word 1 0 = f.a := by change f.a ^ 1 * f.b ^ 0 = f.a; simp
private theorem word_b : f.word 0 1 = f.b := by change f.a ^ 0 * f.b ^ 1 = f.b; simp
private theorem word_mul (i j k l : ZMod 4) :
    f.word i j * f.word k l = f.word (i+k) (j+l) := by
  unfold word
  rw [(f.ab.symm.pow_pow j.val k.val).mul_mul_mul_comm, ← pow_add, ← pow_add]
  simpa only [ZMod.val_add] using
    congrArg₂ (· * ·) (pow_eq_pow_mod (i.val + k.val) f.a_four)
      (pow_eq_pow_mod (j.val + l.val) f.b_four)
private theorem word_inv (i j : ZMod 4) : (f.word i j)⁻¹ = f.word (-i) (-j) := by
  apply inv_eq_of_mul_eq_one_right
  rw [f.word_mul]
  simpa using f.word_zero
private theorem word_pow (i j : ZMod 4) (n : ℕ) :
    f.word i j ^ n = f.word ((n : ZMod 4)*i) ((n : ZMod 4)*j) := by
  induction n with
  | zero => simp [f.word_zero]
  | succ n ih => rw [pow_succ, ih, f.word_mul]; simp [Nat.cast_add, add_mul]
private theorem word_injective [IsMulCommutative D] (hD : Nat.card D = 16)
    (i j k l : ZMod 4) (h : f.word i j = f.word k l) : i = k ∧ j = l := by
  have hh := (f.base_word_eq_iff hD ⟨i.val, ZMod.val_lt i⟩ ⟨j.val, ZMod.val_lt j⟩
    ⟨k.val, ZMod.val_lt k⟩ ⟨l.val, ZMod.val_lt l⟩).mp h
  exact ⟨ZMod.val_injective 4 (congrArg Fin.val hh.1),
    ZMod.val_injective 4 (congrArg Fin.val hh.2)⟩
private theorem word_swap (i j : ZMod 4) :
    (MulAut.conj f.t) (f.word i j) = f.word j i := by
  simp only [word, map_mul, map_pow]
  change (f.t * f.a * f.t⁻¹) ^ i.val * (f.t * f.b * f.t⁻¹) ^ j.val = _
  rw [f.t_a, f.t_b, (f.ab.symm.pow_pow _ _).eq]
private theorem word_g₂ (i j : ZMod 4) :
    (MulAut.conj f.g₂) (f.word i j) = f.word (-i) (2*i-j) := by
  simp only [word, map_mul, map_pow]
  change (f.g₂ * f.a * f.g₂⁻¹) ^ i.val * (f.g₂ * f.b * f.g₂⁻¹) ^ j.val = _
  rw [f.g₂_a, f.g₂_b]
  rw [← f.word_a, ← f.word_b, f.word_inv, f.word_pow, f.word_mul,
    f.word_inv, f.word_pow, f.word_pow, f.word_mul]
  simp [word, show (1 : ZMod 4).val = 1 from rfl, sub_eq_add_neg, mul_comm]
private theorem word_g₁ (i j : ZMod 4) :
    (MulAut.conj f.g₁) (f.word i j) = f.word (-i+2*j) (-j) := by
  simp only [word, map_mul, map_pow]
  change (f.g₁ * f.a * f.g₁⁻¹) ^ i.val * (f.g₁ * f.b * f.g₁⁻¹) ^ j.val = _
  rw [f.g₁_a, f.g₁_b]
  rw [← f.word_a, ← f.word_b, f.word_inv, f.word_pow,
    f.word_inv, f.word_pow, f.word_mul, f.word_pow, f.word_mul]
  simp [word, show (1 : ZMod 4).val = 1 from rfl, mul_comm]

private theorem exists_word [IsMulCommutative D] {x : P} (hx : x ∈ D) :
    ∃ i j : ZMod 4, f.word i j = x := by
  obtain ⟨i, j, hij⟩ := f.exists_base_word hx
  refine ⟨i.val, j.val, ?_⟩
  simpa only [word, ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt j.isLt] using hij
private theorem word_even_mem_four {i j : ZMod 4} (hi : i = 0 ∨ i = 2)
    (hj : j = 0 ∨ j = 2) : f.word i j ∈ W := by
  have ha : f.a ^ 2 ∈ W := f.four.ge (subset_closure (by simp))
  have hb : f.b ^ 2 ∈ W := f.four.ge (subset_closure (by simp))
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
    norm_num only [word, show (2 : ZMod 4).val = 2 from rfl, ZMod.val_zero,
      pow_zero, one_mul, mul_one] <;>
    first | exact W.one_mem | exact ha | exact hb | exact W.mul_mem ha hb
private theorem commutator_inverted {z g : P} (hg : g ^ 2 = 1) :
    (MulAut.conj g) (z * g * z⁻¹ * g⁻¹) = (z * g * z⁻¹ * g⁻¹)⁻¹ := by
  have hi : g⁻¹ = g := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hg)
  simp only [MulAut.conj_apply, mul_inv_rev, inv_inv]
  calc
    _ = g * z * g * z⁻¹ * (g ^ 2)⁻¹ := by simp only [pow_two]; group
    _ = _ := by rw [hg]; simp only [inv_one, mul_one, hi, mul_assoc]

private theorem inversion_coordinates [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D) (hD : Nat.card D = 16)
    (hn : f.z₀ * f.g₁ * f.z₀⁻¹ * f.g₁⁻¹ ∉ W) :
    ∃ i j k l : ZMod 4,
      f.word i j = f.z₀ * f.g₁ * f.z₀⁻¹ * f.g₁⁻¹ ∧
      f.word k l = f.z₀ * f.g₂ * f.z₀⁻¹ * f.g₂⁻¹ ∧
      (i = 1 ∨ i = 3) ∧ (j = 0 ∨ j = 2) ∧
      (k = 0 ∨ k = 2) ∧ (l = 1 ∨ l = 3) := by
  obtain ⟨i,j,hij⟩ := f.exists_word (f.z_commutator_mem_base hDC f.g₁)
  obtain ⟨k,l,hkl⟩ := f.exists_word (f.z_commutator_mem_base hDC f.g₂)
  have h₁ := commutator_inverted (z := f.z₀) f.g₁_two
  have h₂ := commutator_inverted (z := f.z₀) f.g₂_two
  rw [← hij, f.word_g₁, f.word_inv] at h₁
  rw [← hkl, f.word_g₂, f.word_inv] at h₂
  have hrel : f.word i j * (MulAut.conj f.g₁) (f.word k l) =
      f.word k l * (MulAut.conj f.g₂) (f.word i j) := by
    rw [hij, hkl]
    change _ * (f.g₁ * _ * f.g₁⁻¹) = _ * (f.g₂ * _ * f.g₂⁻¹)
    calc
      _ = f.z₀ * (f.g₁ * f.g₂) * f.z₀⁻¹ * (f.g₁ * f.g₂)⁻¹ := by group
      _ = _ := by rw [f.g₁g₂.eq]; group
  rw [f.word_g₁, f.word_g₂, f.word_mul, f.word_mul] at hrel
  have hj := (by decide : ∀ i j : ZMod 4, -i+2*j = -i → j = 0 ∨ j = 2)
    i j (f.word_injective hD _ _ _ _ h₁).1
  have hk := (by decide : ∀ k l : ZMod 4, 2*k-l = -l → k = 0 ∨ k = 2)
    k l (f.word_injective hD _ _ _ _ h₂).2
  have hi : i = 1 ∨ i = 3 := by
    have hall := (by decide : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) i
    rcases hall with hi | hi | hi | hi
    · exact (hn (hij ▸ f.word_even_mem_four (Or.inl hi) hj)).elim
    · exact Or.inl hi
    · exact (hn (hij ▸ f.word_even_mem_four (Or.inr hi) hj)).elim
    · exact Or.inr hi
  have hl := (by decide : ∀ i k l : ZMod 4,
    (i = 1 ∨ i = 3) → (k = 0 ∨ k = 2) →
    i+(-k+2*l) = k + -i → l = 1 ∨ l = 3) i k l hi hk
      (f.word_injective hD _ _ _ _ hrel).1
  exact ⟨i,j,k,l,hij,hkl,hi,hj,hk,hl⟩

private theorem word_mem_base (i j : ZMod 4) : f.word i j ∈ D :=
  D.mul_mem (D.pow_mem (f.base.ge (subset_closure (by simp))) _)
    (D.pow_mem (f.base.ge (subset_closure (by simp))) _)
private theorem word_basis (i j k l : ZMod 4)
    (hi : i = 1 ∨ i = 3) (hj : j = 0 ∨ j = 2)
    (hk : k = 0 ∨ k = 2) (hl : l = 1 ∨ l = 3) :
    D = closure ({f.word i j, f.word k l} : Set P) := by
  have hc := (by decide : ∀ i j k l : ZMod 4,
    (i = 1 ∨ i = 3) → (j = 0 ∨ j = 2) →
    (k = 0 ∨ k = 2) → (l = 1 ∨ l = 3) →
    (2*i = 2 ∧ 2*j = 0 ∧ 2*k = 0 ∧ 2*l = 2) ∧
    (i*i+(-j)*k = 1 ∧ i*j+(-j)*l = 0) ∧
    ((-k)*i+l*k = 0 ∧ (-k)*j+l*l = 1) ∧ (i = l ∨ i = -l)) i j k l hi hj hk hl
  apply le_antisymm
  · apply f.base.le.trans
    apply (closure_le _).mpr
    intro x hx
    have hA : f.word i j ∈ closure ({f.word i j, f.word k l} : Set P) := subset_closure (by simp)
    have hB : f.word k l ∈ closure ({f.word i j, f.word k l} : Set P) := subset_closure (by simp)
    rcases (by simpa using hx : x = f.a ∨ x = f.b) with rfl | rfl
    · have he : f.word i j ^ i.val * f.word k l ^ (-j).val = f.a := by
        rw [f.word_pow, f.word_pow, f.word_mul]
        simpa only [ZMod.natCast_zmod_val, hc.2.1.1, hc.2.1.2] using f.word_a
      rw [← he]
      exact mul_mem (pow_mem hA _) (pow_mem hB _)
    · have he : f.word i j ^ (-k).val * f.word k l ^ l.val = f.b := by
        rw [f.word_pow, f.word_pow, f.word_mul]
        simpa only [ZMod.natCast_zmod_val, hc.2.2.1.1, hc.2.2.1.2] using f.word_b
      rw [← he]
      exact mul_mem (pow_mem hA _) (pow_mem hB _)
  · apply (closure_le _).mpr
    intro x hx
    rcases (by simpa using hx : x = f.word i j ∨ x = f.word k l) with rfl | rfl
    · exact f.word_mem_base _ _
    · exact f.word_mem_base _ _

private theorem rebase_inversion [IsMulCommutative D]
    (hz : f.z₀ ^ 2 = 1) (i j k l : ZMod 4)
    (hi : i = 1 ∨ i = 3) (hj : j = 0 ∨ j = 2)
    (hk : k = 0 ∨ k = 2) (hl : l = 1 ∨ l = 3)
    (hjk : j = k)
    (h₁ : f.z₀ * f.g₁ * f.z₀⁻¹ = f.word i j * f.g₁)
    (h₂ : f.z₀ * f.g₂ * f.z₀⁻¹ = f.word k l * f.g₂) :
    ∃ f' : ActionFrame D W B, f'.InversionRelations := by
  have hc := (by decide : ∀ i j k l : ZMod 4,
    (i = 1 ∨ i = 3) → (j = 0 ∨ j = 2) →
    (k = 0 ∨ k = 2) → (l = 1 ∨ l = 3) →
    (2*i = 2 ∧ 2*j = 0 ∧ 2*k = 0 ∧ 2*l = 2) ∧
    (i*i+(-j)*k = 1 ∧ i*j+(-j)*l = 0) ∧
    ((-k)*i+l*k = 0 ∧ (-k)*j+l*l = 1) ∧ (i = l ∨ i = -l)) i j k l hi hj hk hl
  have ha₂ : f.word i j ^ 2 = f.a ^ 2 := by
    rw [f.word_pow]
    simp only [Nat.cast_ofNat, hc.1.1, hc.1.2.1]
    change f.a ^ 2 * f.b ^ 0 = f.a ^ 2
    simp
  have hb₂ : f.word k l ^ 2 = f.b ^ 2 := by
    rw [f.word_pow]
    simp only [Nat.cast_ofNat, hc.1.2.2.1, hc.1.2.2.2]
    change f.a ^ 0 * f.b ^ 2 = f.b ^ 2
    simp
  have hbase := f.word_basis i j k l hi hj hk hl
  obtain ⟨t', ht', ht'a, ht'b⟩ : ∃ t' : P, (t' = f.t ∨ t' = f.z₀ * f.t) ∧
      (MulAut.conj t') (f.word i j) = f.word k l ∧
      (MulAut.conj t') (f.word k l) = f.word i j := by
    rcases hc.2.2.2 with hil | hil
    · refine ⟨f.t, Or.inl rfl, ?_, ?_⟩ <;> rw [f.word_swap] <;> simp only [hil, hjk]
    · refine ⟨f.z₀ * f.t, Or.inr rfl, ?_, ?_⟩
      · rw [map_mul, MulAut.mul_apply, f.word_swap]
        change f.z₀ * f.word j i * f.z₀⁻¹ = _
        rw [f.z_inverts_base (f.word_mem_base _ _), f.word_inv]
        congr 1
        · subst k; rcases hj with rfl | rfl <;> decide
        · rw [hil, neg_neg]
      · rw [map_mul, MulAut.mul_apply, f.word_swap]
        change f.z₀ * f.word l k * f.z₀⁻¹ = _
        rw [f.z_inverts_base (f.word_mem_base _ _), f.word_inv]
        congr 1
        · exact hil.symm
        · subst k; rcases hj with rfl | rfl <;> decide
  let f' : ActionFrame D W B :=
    { f with
      a := f.word i j
      b := f.word k l
      t := t'
      a_four := by rw [show 4 = 2*2 from rfl, pow_mul, ha₂, ← pow_mul]; exact f.a_four
      b_four := by rw [show 4 = 2*2 from rfl, pow_mul, hb₂, ← pow_mul]; exact f.b_four
      ab := D.le_centralizer (f.word_mem_base k l) _ (f.word_mem_base i j)
      base := hbase
      four := by rw [ha₂, hb₂]; exact f.four
      g₁_a := by
        change (MulAut.conj f.g₁) (f.word i j) = _
        rw [f.word_g₁, f.word_inv, hc.1.2.1, add_zero]
      g₁_b := by
        change (MulAut.conj f.g₁) (f.word k l) = _
        rw [f.word_g₁, f.word_pow, f.word_inv, f.word_mul]
        simp only [Nat.cast_ofNat, hc.1.1, hc.1.2.1, hc.1.2.2.2, zero_add, add_comm, add_zero]
      g₂_a := by
        change (MulAut.conj f.g₂) (f.word i j) = _
        rw [f.word_g₂, f.word_inv, f.word_pow, f.word_mul]
        simp only [Nat.cast_ofNat, hc.1.1, hc.1.2.2.1, hc.1.2.2.2, add_zero,
          sub_eq_add_neg, add_comm]
      g₂_b := by
        change (MulAut.conj f.g₂) (f.word k l) = _
        rw [f.word_g₂, f.word_inv, hc.1.2.2.1, zero_sub]
      z₀_a := f.z_inverts_base (f.word_mem_base i j)
      z₀_b := f.z_inverts_base (f.word_mem_base k l)
      t_a := ht'a
      t_b := ht'b
      generate := by
        let K := closure ({f.word i j, f.word k l, f.g₁, f.g₂, t', f.z₀} : Set P)
        have hDK : D ≤ K := by
          apply hbase.le.trans
          apply (closure_le _).mpr
          intro x hx
          rcases (by simpa using hx : x = f.word i j ∨ x = f.word k l) with rfl | rfl
          · exact subset_closure (by simp)
          · exact subset_closure (by simp)
        have hzK : f.z₀ ∈ K := subset_closure (by simp)
        have htK : f.t ∈ K := by
          have h : t' ∈ K := subset_closure (by simp)
          rcases ht' with rfl | rfl
          · exact h
          · simpa only [inv_mul_cancel_left] using K.mul_mem (K.inv_mem hzK) h
        apply top_unique
        apply f.generate.ge.trans
        apply (closure_le _).mpr
        intro x hx
        rcases (by simpa using hx : x = f.a ∨ x = f.b ∨ x = f.g₁ ∨
          x = f.g₂ ∨ x = f.t ∨ x = f.z₀) with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hDK (f.base.ge (subset_closure (by simp)))
        · exact hDK (f.base.ge (subset_closure (by simp)))
        · exact subset_closure (by simp)
        · exact subset_closure (by simp)
        · exact htK
        · exact hzK }
  exact ⟨f', ⟨hz, h₁, h₂⟩⟩

/-- A nontrivial inversion commutator modulo W forces the two inversion
commutators to generate the whole base. No condition on the inversion square
is needed. -/
public theorem base_eq_closure_inversion_commutators [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D) (hD : Nat.card D = 16)
    (hn : f.z₀ * f.g₁ * f.z₀⁻¹ * f.g₁⁻¹ ∉ W) :
    D = closure ({f.z₀ * f.g₁ * f.z₀⁻¹ * f.g₁⁻¹,
      f.z₀ * f.g₂ * f.z₀⁻¹ * f.g₂⁻¹} : Set P) := by
  obtain ⟨i,j,k,l,hij,hkl,hi,hj,hk,hl⟩ := f.inversion_coordinates hDC hD hn
  simpa only [hij, hkl] using f.word_basis i j k l hi hj hk hl

private theorem commutator_correct_z (d z g : P) :
    (d*z)*g*(d*z)⁻¹*g⁻¹ = d*(z*g*z⁻¹*g⁻¹)*((MulAut.conj g) d⁻¹) := by
  change _ = d*(z*g*z⁻¹*g⁻¹)*(g*d⁻¹*g⁻¹)
  group

/-- A nontrivial inversion commutator modulo the four supplies the normalized
basis. One base correction equalizes the off-diagonal coordinates; if needed,
multiplication of the swap lift by the inverter changes the sign of its action. -/
public theorem exists_inversionRelations_of_square_and_commutator
    [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D) (hD : Nat.card D = 16)
    (hz : f.z₀ ^ 2 = 1) (hn : f.z₀ * f.g₁ * f.z₀⁻¹ * f.g₁⁻¹ ∉ W) :
    ∃ f' : ActionFrame D W B, f'.InversionRelations := by
  obtain ⟨i,j,k,l,hij,hkl,hi,hj,hk,hl⟩ := f.inversion_coordinates hDC hD hn
  obtain ⟨u,hu,hju⟩ := (by decide : ∀ j k : ZMod 4,
    (j = 0 ∨ j = 2) → (k = 0 ∨ k = 2) →
    ∃ u : ZMod 4, (u = 0 ∨ u = 1) ∧ j = k+2*u) j k hj hk
  let d := f.word u 0
  have hd : d ∈ D := f.word_mem_base u 0
  let f₀ := f.correctOuter 1 d D.one_mem hd
  have h₀z : f₀.z₀ ^ 2 = 1 := (f.z_correction_square hd).trans hz
  have hc₁ : f₀.z₀ * f₀.g₁ * f₀.z₀⁻¹ * f₀.g₁⁻¹ = f₀.word (i+2*u) j := by
    change (d*f.z₀)*f.g₁*(d*f.z₀)⁻¹*f.g₁⁻¹ = f.word (i+2*u) j
    rw [commutator_correct_z, ← hij]
    dsimp only [d]
    rw [f.word_inv, f.word_g₁, f.word_mul, f.word_mul]
    congr 1 <;> ring
  have hc₂ : f₀.z₀ * f₀.g₂ * f₀.z₀⁻¹ * f₀.g₂⁻¹ = f₀.word (k+2*u) (l-2*u) := by
    change (d*f.z₀)*f.g₂*(d*f.z₀)⁻¹*f.g₂⁻¹ = f.word (k+2*u) (l-2*u)
    rw [commutator_correct_z, ← hkl]
    dsimp only [d]
    rw [f.word_inv, f.word_g₂, f.word_mul, f.word_mul]
    congr 1 <;> ring
  have hc := (by decide : ∀ i k l u : ZMod 4,
    (i = 1 ∨ i = 3) → (k = 0 ∨ k = 2) → (l = 1 ∨ l = 3) → (u = 0 ∨ u = 1) →
    (i+2*u = 1 ∨ i+2*u = 3) ∧ (k+2*u = 0 ∨ k+2*u = 2) ∧
      (l-2*u = 1 ∨ l-2*u = 3)) i k l u hi hk hl hu
  exact f₀.rebase_inversion h₀z (i+2*u) j (k+2*u) (l-2*u)
    hc.1 hj hc.2.1 hc.2.2 hju
    (mul_inv_eq_iff_eq_mul.mp hc₁) (mul_inv_eq_iff_eq_mul.mp hc₂)
end ExoticTwoGroup.ActionFrame
