module

public import Theory.SpecificGroups.ExoticTwoGroup.LiftCorrection
import Mathlib.Tactic

/-!
# Completing the swap lift in the exotic extension

Normalized inversion relations force the swap's inner-generator defect into
W. The outer commutator is either trivial or the product of the two basis
squares. Multiplication by a * b⁻¹ kills the latter possibility while keeping
the swap involutory. Replacing the second inner generator by the conjugate of
the first then supplies every lift relation, preserves generation, and keeps
the inner generators in B because W ≤ B.

The finite coordinate constraints are proved from uniqueness of the sixteen
base words. No ambient fusion or simplicity assumption is used here.

Source: MacWilliams, Trans. AMS 150 (1970), Case 2.3.2, pp.396–399;
Janko–Thompson, Math. Z. 113 (1970), 1.4(c), printed p.386.
-/

set_option linter.unusedSimpArgs false
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

private theorem defect_equations [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D) (hz : f.InversionRelations)
    (ht : f.t ^ 2 = 1) :
    let e := f.t * f.g₁ * f.t⁻¹ * f.g₂⁻¹
    let d := f.t * f.z₀ * f.t⁻¹ * f.z₀⁻¹
    e * (MulAut.conj f.g₂) e = 1 ∧
    (MulAut.conj f.t) d = d⁻¹ ∧
    e ^ 2 = d * (MulAut.conj f.g₂) d⁻¹ := by
  dsimp only
  let e := f.t * f.g₁ * f.t⁻¹ * f.g₂⁻¹
  let d := f.t * f.z₀ * f.t⁻¹ * f.z₀⁻¹
  change e * (MulAut.conj f.g₂) e = 1 ∧
    (MulAut.conj f.t) d = d⁻¹ ∧ e ^ 2 = d * (MulAut.conj f.g₂) d⁻¹
  have he : e ∈ D := f.t_g₁_defect_mem_base hDC
  have hd : d ∈ D := by
    simpa only [mul_inv_rev, inv_inv, ← mul_assoc] using
      D.inv_mem (f.z_commutator_mem_base hDC f.t)
  have hb : f.b ∈ D := f.base.ge (subset_closure (by simp))
  have heg : e * f.g₂ = (MulAut.conj f.t) f.g₁ := by dsimp [e]; group
  have hdz : d * f.z₀ = (MulAut.conj f.t) f.z₀ := by dsimp [d]; group
  have hti : f.t⁻¹ = f.t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht)
  refine ⟨?_, ?_, ?_⟩
  · calc
      e * (MulAut.conj f.g₂) e = (e * f.g₂) ^ 2 * (f.g₂ ^ 2)⁻¹ := by
        change e * (f.g₂ * e * f.g₂⁻¹) = _
        simp only [pow_two]; group
      _ = 1 := by rw [heg, ← map_pow, f.g₁_two, f.g₂_two, map_one]; simp
  · change f.t * d * f.t⁻¹ = d⁻¹
    dsimp [d]
    calc
      _ = f.t ^ 2 * f.z₀ * f.t⁻¹ * f.z₀⁻¹ * f.t⁻¹ := by simp only [pow_two]; group
      _ = _ := by simp only [ht, one_mul, mul_inv_rev, inv_inv, hti, mul_assoc]
  · have hrel : (MulAut.conj (d * f.z₀)) (e * f.g₂) = f.b * (e * f.g₂) := by
      rw [heg, hdz]
      calc
        _ = (MulAut.conj f.t) (f.z₀ * f.g₁ * f.z₀⁻¹) := by
          simp only [MulAut.conj_apply]; group
        _ = _ := by
          rw [hz.z₀_g₁, map_mul]
          exact congrArg (· * (MulAut.conj f.t) f.g₁) f.t_a
    have hh : d * e⁻¹ * f.b * ((MulAut.conj f.g₂) d⁻¹) = f.b * e := by
      have hh := congrArg (fun x => x * f.g₂⁻¹) hrel
      change (d * f.z₀) * (e * f.g₂) * (d * f.z₀)⁻¹ * f.g₂⁻¹ = _ at hh
      have hc : (d * f.z₀) * (e * f.g₂) * (d * f.z₀)⁻¹ * f.g₂⁻¹ =
          d * (f.z₀ * e * f.z₀⁻¹) * (f.z₀ * f.g₂ * f.z₀⁻¹) * d⁻¹ * f.g₂⁻¹ := by group
      rw [hc, f.z_inverts_base he, hz.z₀_g₂] at hh
      simpa only [MulAut.conj_apply, mul_assoc, mul_inv_cancel, mul_one] using hh
    have hde : Commute d e⁻¹ := (D.le_centralizer hd _ (D.inv_mem he)).symm
    have hdb : Commute d f.b := (D.le_centralizer hd _ hb).symm
    have heb : Commute e f.b := (D.le_centralizer he _ hb).symm
    calc
      e ^ 2 = (e * f.b⁻¹) * (f.b * e) := by simp only [pow_two]; group
      _ = (e * f.b⁻¹) * (d * e⁻¹ * f.b * ((MulAut.conj f.g₂) d⁻¹)) := by rw [hh]
      _ = d * (MulAut.conj f.g₂) d⁻¹ := by
        rw [hde.eq, mul_assoc e⁻¹ d f.b, hdb.eq, ← mul_assoc]
        rw [← mul_assoc e⁻¹ f.b d, heb.inv_left.eq]
        group

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
    norm_num only [word, show (2 : ZMod 4).val = 2 from rfl, ZMod.val_zero, pow_zero, one_mul, mul_one] <;>
    first | exact W.one_mem | exact ha | exact hb | exact W.mul_mem ha hb

private theorem defects_in_four [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D) (hD : Nat.card D = 16)
    (hz : f.InversionRelations) (ht : f.t ^ 2 = 1) :
    f.t * f.g₁ * f.t⁻¹ * f.g₂⁻¹ ∈ W ∧
    (f.t * f.z₀ * f.t⁻¹ * f.z₀⁻¹ = 1 ∨
      f.t * f.z₀ * f.t⁻¹ * f.z₀⁻¹ = f.a ^ 2 * f.b ^ 2) := by
  let e := f.t * f.g₁ * f.t⁻¹ * f.g₂⁻¹
  let d := f.t * f.z₀ * f.t⁻¹ * f.z₀⁻¹
  have he : e ∈ D := f.t_g₁_defect_mem_base hDC
  have hd : d ∈ D := by
    simpa only [mul_inv_rev, inv_inv, ← mul_assoc] using
      D.inv_mem (f.z_commutator_mem_base hDC f.t)
  obtain ⟨i,j,hij⟩ := f.exists_word he
  obtain ⟨k,l,hkl⟩ := f.exists_word hd
  obtain ⟨heq, hdq, hed⟩ := f.defect_equations hDC hz ht
  change e * (MulAut.conj f.g₂) e = 1 at heq
  change (MulAut.conj f.t) d = d⁻¹ at hdq
  change e ^ 2 = d * (MulAut.conj f.g₂) d⁻¹ at hed
  rw [← hij, f.word_g₂, f.word_mul, ← f.word_zero] at heq
  rw [← hkl, f.word_swap, f.word_inv] at hdq
  rw [← hij, ← hkl, f.word_pow, f.word_inv, f.word_g₂, f.word_mul] at hed
  have hc := (by decide : ∀ i j k l : ZMod 4,
    (i + -i = 0 ∧ j + (2*i-j) = 0) →
    (l = -k ∧ k = -l) →
    (2*i = k + -(-k) ∧ 2*j = l + (2*(-k)-(-l))) →
    (i = 0 ∨ i = 2) ∧ (j = 0 ∨ j = 2) ∧
      ((k = 0 ∧ l = 0) ∨ (k = 2 ∧ l = 2))) i j k l
    (f.word_injective hD _ _ _ _ heq) (f.word_injective hD _ _ _ _ hdq)
    (f.word_injective hD _ _ _ _ hed)
  refine ⟨?_, ?_⟩
  · change e ∈ W
    rw [← hij]
    exact f.word_even_mem_four hc.1 hc.2.1
  · rcases hc.2.2 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl (hkl.symm.trans f.word_zero)
    · exact Or.inr (hkl.symm.trans (by rfl))

private theorem exists_commuting_frame [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D) (hD : Nat.card D = 16)
    (hz : f.InversionRelations) (ht : f.t ^ 2 = 1) :
    ∃ f' : ActionFrame D W B,
      f'.InversionRelations ∧ f'.t ^ 2 = 1 ∧ Commute f'.t f'.z₀ := by
  obtain ⟨_, hd⟩ := f.defects_in_four hDC hD hz ht
  rcases hd with hd | hd
  · refine ⟨f, hz, ht, ?_⟩
    change f.t * f.z₀ = f.z₀ * f.t
    apply mul_inv_eq_one.mp
    simpa only [mul_inv_rev, ← mul_assoc] using hd
  · let c := f.word 1 (-1)
    have hc : c ∈ D := D.mul_mem
      (D.pow_mem (f.base.ge (subset_closure (by simp))) _)
      (D.pow_mem (f.base.ge (subset_closure (by simp))) _)
    have ht' : (c * f.t) ^ 2 = 1 := by
      calc
        (c * f.t) ^ 2 = c * ((MulAut.conj f.t) c) * f.t ^ 2 := by
          change _ = c * (f.t * c * f.t⁻¹) * f.t ^ 2
          simp only [pow_two]; group
        _ = 1 := by
          dsimp only [c]
          rw [f.word_swap, ht, mul_one, f.word_mul]
          exact f.word_zero
    have htz' : Commute (c * f.t) f.z₀ := by
      have hh : (c * f.t) * f.z₀ * (c * f.t)⁻¹ * f.z₀⁻¹ = 1 := by
        calc
          _ = c * (f.t * f.z₀ * f.t⁻¹ * f.z₀⁻¹) *
              (f.z₀ * c⁻¹ * f.z₀⁻¹) := by group
          _ = c * (f.a ^ 2 * f.b ^ 2) * c := by
            rw [hd, f.z_inverts_base (D.inv_mem hc), inv_inv]
          _ = 1 := by
            change f.word 1 (-1) * f.word 2 2 * f.word 1 (-1) = 1
            rw [f.word_mul, f.word_mul]
            exact f.word_zero
      change (c * f.t) * f.z₀ = f.z₀ * (c * f.t)
      apply mul_inv_eq_one.mp
      simpa only [mul_inv_rev, ← mul_assoc] using hh
    refine ⟨f.correctOuter c 1 hc D.one_mem, ⟨?_, ?_, ?_⟩, ht', ?_⟩
    · simpa only [correctOuter_z₀, one_mul] using hz.z₀_two
    · simpa only [correctOuter_z₀, correctOuter_g₁, correctOuter_a, one_mul] using hz.z₀_g₁
    · simpa only [correctOuter_z₀, correctOuter_g₂, correctOuter_b, one_mul] using hz.z₀_g₂
    · simpa only [correctOuter_z₀, correctOuter_t, one_mul] using htz'

private theorem replace_second [D.Normal] [IsMulCommutative D] [IsMulCommutative B]
    (hDC : centralizer (D : Set P) ≤ D) (hD : Nat.card D = 16) (hWB : W ≤ B)
    (hz : f.InversionRelations) (ht : f.t ^ 2 = 1) (htz : Commute f.t f.z₀) :
    ∃ f' : ActionFrame D W B, f'.LiftRelations := by
  let e := f.t * f.g₁ * f.t⁻¹ * f.g₂⁻¹
  have heD : e ∈ D := f.t_g₁_defect_mem_base hDC
  have heW : e ∈ W := (f.defects_in_four hDC hD hz ht).1
  have hgB : e * f.g₂ ∈ B := B.mul_mem (hWB heW) f.g₂_mem
  have hg : e * f.g₂ = (MulAut.conj f.t) f.g₁ := by dsimp [e]; group
  have hconj (x : P) (hx : x ∈ D) :
      (e * f.g₂) * x * (e * f.g₂)⁻¹ = f.g₂ * x * f.g₂⁻¹ := by
    calc
      _ = e * (f.g₂ * x * f.g₂⁻¹) * e⁻¹ := by group
      _ = _ := by
        rw [← D.le_centralizer heD _ ((inferInstance : D.Normal).conj_mem x hx f.g₂),
          mul_inv_cancel_right]
  have hzg : f.z₀ * (e * f.g₂) * f.z₀⁻¹ = f.b * (e * f.g₂) := by
    change (MulAut.conj f.z₀) (e * f.g₂) = _
    rw [hg]
    calc
      _ = (MulAut.conj f.t) ((MulAut.conj f.z₀) f.g₁) :=
        congrArg (fun u : MulAut P => u f.g₁) (htz.symm.map (MulAut.conj)).eq
      _ = _ := by
        change (MulAut.conj f.t) (f.z₀ * f.g₁ * f.z₀⁻¹) = _
        rw [hz.z₀_g₁, map_mul]
        exact congrArg (· * (MulAut.conj f.t) f.g₁) f.t_a
  let f' : ActionFrame D W B :=
    { f with
      g₂ := e * f.g₂
      g₂_mem := hgB
      g₂_two := by rw [hg, ← map_pow, f.g₁_two, map_one]
      g₁g₂ := B.le_centralizer hgB _ f.g₁_mem
      g₂_a := by rw [hconj _ (f.base.ge (subset_closure (by simp))), f.g₂_a]
      g₂_b := by rw [hconj _ (f.base.ge (subset_closure (by simp))), f.g₂_b]
      generate := by
        let K := closure ({f.a, f.b, f.g₁, e * f.g₂, f.t, f.z₀} : Set P)
        have hDK : D ≤ K := by
          apply f.base.le.trans
          apply (closure_le _).mpr
          intro x hx
          rcases (by simpa using hx : x = f.a ∨ x = f.b) with rfl | rfl
          · exact subset_closure (by simp)
          · exact subset_closure (by simp)
        have hgK : f.g₂ ∈ K := by
          have hh := K.mul_mem (K.inv_mem (hDK heD))
            (subset_closure (by simp : e * f.g₂ ∈
              ({f.a, f.b, f.g₁, e * f.g₂, f.t, f.z₀} : Set P)))
          simpa only [inv_mul_cancel_left] using hh
        apply top_unique
        apply f.generate.ge.trans
        apply (closure_le _).mpr
        intro x hx
        rcases (by simpa using hx : x = f.a ∨ x = f.b ∨ x = f.g₁ ∨
          x = f.g₂ ∨ x = f.t ∨ x = f.z₀) with rfl | rfl | rfl | rfl | rfl | rfl
        · exact subset_closure (by simp)
        · exact subset_closure (by simp)
        · exact subset_closure (by simp)
        · exact hgK
        · exact subset_closure (by simp)
        · exact subset_closure (by simp) }
  exact ⟨f', f'.liftRelations_of_inversion_and_swap
    ⟨hz.z₀_two, hz.z₀_g₁, hzg⟩ ht htz hg.symm⟩

/-- Normalized inversion relations suffice for all lift relations: the swap
lift and the second inner generator can be corrected inside the marked base. -/
public theorem exists_liftRelations_of_inversion [D.Normal] [IsMulCommutative D]
    [IsMulCommutative B] (hDC : centralizer (D : Set P) ≤ D)
    (hD : Nat.card D = 16) (hWB : W ≤ B) (hz : f.InversionRelations) :
    ∃ f' : ActionFrame D W B, f'.LiftRelations := by
  obtain ⟨f₁, hz₁, ht₁⟩ := f.exists_involutory_t_frame hDC hD hz
  obtain ⟨f₂, hz₂, ht₂, htz₂⟩ := f₁.exists_commuting_frame hDC hD hz₁ ht₁
  exact f₂.replace_second hDC hD hWB hz₂ ht₂ htz₂
end ExoticTwoGroup.ActionFrame
