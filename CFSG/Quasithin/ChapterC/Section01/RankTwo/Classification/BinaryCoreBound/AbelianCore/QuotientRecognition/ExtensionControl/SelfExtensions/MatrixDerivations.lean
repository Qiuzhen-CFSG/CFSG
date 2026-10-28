module

public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary
import Mathlib.Tactic.FinCases

/-!
# Inner derivations of the binary natural matrix representation

A derivation into the natural matrix bimodule is determined by a Singer element
and one transvection. Elementary transvection words certify generation in the
actual group. The relation s^7 = 1 first permits normalization at s; the relations
t^2 = (st)^4 = (s^2 t)^3 = 1 then give a primitive commuting with s. Both linear
calculations are finite, kernel-checked calculations on 3-by-3 binary matrices.

This proves vanishing of the self-extension obstruction for the binary natural
module, used in Aschbacher–Smith B.4.9(2)(i), printed pp.92–94, combined manuscript
of 1 March 2004. It does not assume the FF condition.
-/

@[expose] public section
open Matrix
namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition.ExtensionControl.SelfExtensions.MatrixDerivations
abbrev SL := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
abbrev Mat := Matrix (Fin 3) (Fin 3) (ZMod 2)
private def s : SL := ⟨!![0,0,1; 1,0,1; 0,1,0], by decide⟩
private def t : SL := ⟨!![1,1,0; 0,1,0; 0,0,1], by decide⟩
private def powerValue (g x : Mat) : ℕ → Mat
  | 0 => 0
  | n+1 => g ^ n * x + powerValue g x n * g

private def firstPrimitive (x : Mat) : Mat :=
  !![0, x 0 0, x 0 0 + x 0 2 + x 1 0 + x 1 2;
     0, x 1 0, x 0 1 + x 0 2 + x 1 0 + x 1 1 + x 1 2;
     0, x 0 0 + x 0 1 + x 0 2 + x 1 0 + x 1 2, x 0 0 + x 0 2]

private def secondPrimitive (x : Mat) : Mat :=
  (x * t.val) 0 0 • s.val + (x * t.val) 2 1 • s.val ^ 2

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
private lemma first_calc : ∀ x : Mat, powerValue s.val x 7 = 0 →
    s.val * firstPrimitive x - firstPrimitive x * s.val = x := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
private lemma second_calc : ∀ x : Mat,
    powerValue t.val x 2 = 0 →
    powerValue (s * t).val (s.val * x) 4 = 0 →
    powerValue (s ^ 2 * t).val ((s ^ 2).val * x) 3 = 0 →
    s.val * secondPrimitive x - secondPrimitive x * s.val = 0 ∧
    t.val * secondPrimitive x - secondPrimitive x * t.val = x := by
  decide +kernel

private def rootWord (i j : Fin 3) : List SL :=
  if i = 0 ∧ j = 1 then [t] else
  if i = 0 ∧ j = 2 then [s,s,s,t,s,s,s,t,s,s] else
  if i = 1 ∧ j = 0 then [s,s,s,s,t,s,s,s,t,s] else
  if i = 1 ∧ j = 2 then [s,s,t,s,t,s,t] else
  if i = 2 ∧ j = 0 then [s,s,s,s,t,s,s,t] else
  if i = 2 ∧ j = 1 then [s,s,s,s,s,t,s,t,s,s,s] else []

private lemma rootWord_eq : ∀ (i j : Fin 3) (hij : i ≠ j),
    (rootWord i j).prod = SpecialLinearGroup.transvection hij (1 : ZMod 2) := by
  decide +kernel

private lemma rootWord_letters (i j : Fin 3) : ∀ x ∈ rootWord i j, x = s ∨ x = t := by
  unfold rootWord
  split_ifs <;> simp_all

private lemma generator_induction (P : SL → Prop) (hone : P 1) (hs : P s) (ht : P t)
    (hmul : ∀ a b, P a → P b → P (a * b)) (g : SL) : P g := by
  have hword (w : List SL) (hw : ∀ x ∈ w, x = s ∨ x = t) : P w.prod := by
    induction w with
    | nil => exact hone
    | cons a w ih =>
      apply hmul
      · rcases hw a (by simp) with rfl | rfl
        · exact hs
        · exact ht
      · exact ih (fun x hx => hw x (by simp [hx]))
  apply Representation.OneCohomology.SLHigherNatural.transvection_induction P ?_ hmul g
  intro i j hij c
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl
  · have hz : SpecialLinearGroup.transvection hij (0 : ZMod 2) = 1 := by
      apply Subtype.ext
      simp
    rwa [hz]
  · rw [← rootWord_eq i j hij]
    exact hword _ (rootWord_letters i j)

private lemma s_seven : s ^ 7 = 1 := by decide +kernel
private lemma t_two : t ^ 2 = 1 := by decide +kernel
private lemma st_four : (s * t) ^ 4 = 1 := by decide +kernel
private lemma sst_three : (s ^ 2 * t) ^ 3 = 1 := by decide +kernel



def IsDerivation (d : SL → Mat) : Prop :=
  ∀ g h, d (g * h) = g.val * d h + d g * h.val

private lemma derivation_one {d : SL → Mat} (hd : IsDerivation d) : d 1 = 0 := by
  have h := hd 1 1
  simpa using h

private lemma derivation_power {d : SL → Mat} (hd : IsDerivation d) (g : SL) (n : ℕ) :
    d (g ^ n) = powerValue g.val (d g) n := by
  induction n with
  | zero => exact derivation_one hd
  | succ n ih =>
    rw [pow_succ, hd, ih]
    rfl

private lemma inner_derivation (b : Mat) : IsDerivation (fun g => g.val * b - b * g.val) := by
  intro g h
  simp only [SpecialLinearGroup.coe_mul, mul_sub, sub_mul, mul_assoc]
  abel

private lemma sub_derivation {d e : SL → Mat} (hd : IsDerivation d) (he : IsDerivation e) :
    IsDerivation (fun g => d g - e g) := by
  intro g h
  change d (g * h) - e (g * h) = g.val * (d h - e h) + (d g - e g) * h.val
  rw [hd, he, mul_sub, sub_mul]
  abel

private lemma derivation_ext {d e : SL → Mat} (hd : IsDerivation d) (he : IsDerivation e)
    (hs : d s = e s) (ht : d t = e t) : d = e := by
  funext g
  apply generator_induction (fun g => d g = e g) ?_ hs ht ?_ g
  · rw [derivation_one hd, derivation_one he]
  · intro a b ha hb
    rw [hd, he, ha, hb]

lemma derivation_inner (d : SL → Mat) (hd : IsDerivation d) :
    ∃ b : Mat, ∀ g, d g = g.val * b - b * g.val := by
  let b := firstPrimitive (d s)
  have hb : s.val * b - b * s.val = d s := by
    apply first_calc
    rw [← derivation_power hd, s_seven, derivation_one hd]
  let e : SL → Mat := fun g => d g - (g.val * b - b * g.val)
  have he : IsDerivation e := sub_derivation hd (inner_derivation b)
  have hes : e s = 0 := by dsimp [e]; rw [hb, sub_self]
  have hes2 : e (s ^ 2) = 0 := by rw [pow_two, he, hes]; simp
  have he1 := derivation_one he
  have ht : powerValue t.val (e t) 2 = 0 := by
    rw [← derivation_power he, t_two, he1]
  have hst : powerValue (s * t).val (s.val * e t) 4 = 0 := by
    have hh : e (s * t) = s.val * e t := by rw [he, hes]; simp
    rw [← hh, ← derivation_power he, st_four, he1]
  have hsst : powerValue (s ^ 2 * t).val ((s ^ 2).val * e t) 3 = 0 := by
    have hh : e (s ^ 2 * t) = (s ^ 2).val * e t := by rw [he, hes2]; simp
    rw [← hh, ← derivation_power he, sst_three, he1]
  obtain ⟨hcs, hct⟩ := second_calc (e t) ht hst hsst
  have hinner := derivation_ext he (inner_derivation (secondPrimitive (e t)))
    (hes.trans hcs.symm) hct.symm
  refine ⟨b + secondPrimitive (e t), fun g => ?_⟩
  have hg := congrFun hinner g
  change d g - (g.val * b - b * g.val) =
    g.val * secondPrimitive (e t) - secondPrimitive (e t) * g.val at hg
  rw [mul_add, add_mul]
  rw [sub_eq_iff_eq_add] at hg
  rw [hg]
  abel
end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition.ExtensionControl.SelfExtensions.MatrixDerivations
