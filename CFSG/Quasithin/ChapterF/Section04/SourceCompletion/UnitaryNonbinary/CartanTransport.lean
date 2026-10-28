module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.NativeWeyl
import Mathlib.Tactic.Group

/-!
# Cartan fixation of a full-overlap rotation defect

Faithful endpoint maps transfer conjugation by the two native reflections
on any native Cartan set they normalize. If the native rotation has nth
power one, its nth power in the completion fixes that Cartan pointwise.
When the full-middle defect has square one, it also fixes each reflection.
The exact inner intersections ensure it preserves both native parabolics.

These are local constraints on the possible outer defect, not a proof that
it is trivial. They do not replace the full overlap by its inner subgroup.
The concrete consumers use the entire diagonal Cartan, including nonfixed
field entries. Source: the direct apartment route in Aschbacher–Smith
F.4.10,16–17, printed pp.279,282–283 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.SourceExtension
open Subgroup Theory.GroupTheory
variable {B : Type*} [Group B] {P₀ P₁ : Subgroup B}
variable (E : SourceExtension P₀ P₁) {M : Type*} [Group M]
variable (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))

private theorem aut_conj (a : MulAut B) (b : B) :
    a * MulAut.conj b * a⁻¹ = MulAut.conj (a b) := by
  ext x
  simp [MulAut.conj_apply]

theorem middle_preserves_left
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (a : E.middle) (b : B) : a.val b ∈ P₀ ↔ b ∈ P₀ := by
  have forward (a : E.middle) (b : B) (hb : b ∈ P₀) : a.val b ∈ P₀ := by
    apply (E.conj_mem_left_iff hi _).mp
    rw [←aut_conj]
    exact E.left.mul_mem (E.left.mul_mem a.property.1
      ((E.conj_mem_left_iff hi b).mpr hb)) (E.left.inv_mem a.property.1)
  refine ⟨fun h => ?_,forward a b⟩
  simpa using forward a⁻¹ (a.val b) h

theorem middle_preserves_right
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (a : E.middle) (b : B) : a.val b ∈ P₁ ↔ b ∈ P₁ := by
  have forward (a : E.middle) (b : B) (hb : b ∈ P₁) : a.val b ∈ P₁ := by
    apply (E.conj_mem_right_iff hi _).mp
    rw [←aut_conj]
    exact E.right.mul_mem (E.right.mul_mem a.property.2
      ((E.conj_mem_right_iff hi b).mpr hb)) (E.right.inv_mem a.property.2)
  refine ⟨fun h => ?_,forward a b⟩
  simpa using forward a⁻¹ (a.val b) h

private theorem reflection_commutes (s t : M) (hs : s^2=1) (ht : t^2=1)
    (n : ℕ) (h : ((t*s)^n)^2=1) : Commute ((t*s)^n) s ∧ Commute ((t*s)^n) t := by
  have hsi : s⁻¹=s := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs)
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht)
  have hri : ((t*s)^n)⁻¹=(t*s)^n :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using h)
  have hsconj : s*(t*s)*s⁻¹=(t*s)⁻¹ := by
    rw [←mul_assoc s t s,mul_inv_cancel_right,_root_.mul_inv_rev,hsi,hti]
  have htconj : t*(t*s)*t⁻¹=(t*s)⁻¹ := by
    rw [_root_.mul_inv_rev,hsi,hti]
    calc
      t*(t*s)*t = (t*t)*s*t := by group
      _ = s*t := by rw [←pow_two,ht,one_mul]
  constructor
  · apply Commute.symm
    apply mul_inv_eq_iff_eq_mul.mp
    rw [←conj_pow,hsconj,inv_pow,hri]
  · apply Commute.symm
    apply mul_inv_eq_iff_eq_mul.mp
    rw [←conj_pow,htconj,inv_pow,hri]

theorem rotation_defect_fixes_reflections
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (s : P₀) (t : P₁) (hs : s^2=1) (ht : t^2=1)
    (n : ℕ) (a : E.middle) (ha : c.middle a=E.nativeRotation c s t^n)
    (ha2 : a^2=1) : a.val s.val=s.val ∧ a.val t.val=t.val := by
  have hs' : (E.innerLeft c s)^2=1 := by rw [←map_pow,hs,map_one]
  have ht' : (E.innerRight c t)^2=1 := by rw [←map_pow,ht,map_one]
  have h2 : (E.nativeRotation c s t^n)^2=1 := by rw [←ha,←map_pow,ha2,map_one]
  obtain ⟨hl,hr⟩ := reflection_commutes (E.innerLeft c s) (E.innerRight c t) hs' ht' n h2
  have hl' : a.val * MulAut.conj s.val = MulAut.conj s.val * a.val := by
    change ((E.amalgam.left a * E.nativeLeft s : E.left) : MulAut B) =
      ((E.nativeLeft s * E.amalgam.left a : E.left) : MulAut B)
    apply congrArg Subtype.val
    apply c.left_injective
    rw [map_mul,map_mul]
    change c.middle a*E.innerLeft c s=E.innerLeft c s*c.middle a
    rw [ha]
    exact hl.eq
  have hr' : a.val * MulAut.conj t.val = MulAut.conj t.val * a.val := by
    have hc := DFunLike.congr_fun c.compatible a
    change c.middle a=c.right (E.amalgam.right a) at hc
    change ((E.amalgam.right a * E.nativeRight t : E.right) : MulAut B) =
      ((E.nativeRight t * E.amalgam.right a : E.right) : MulAut B)
    apply congrArg Subtype.val
    apply c.right_injective
    rw [map_mul,map_mul,←hc]
    change c.middle a*E.innerRight c t=E.innerRight c t*c.middle a
    rw [ha]
    exact hr.eq
  constructor
  · apply hi
    rw [←aut_conj,hl',mul_inv_cancel_right]
  · apply hi
    rw [←aut_conj,hr',mul_inv_cancel_right]

private theorem middle_fixed_of_commute
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (a : E.middle) (b : (P₀ ⊓ P₁ : Subgroup B))
    (h : Commute (c.middle a) (E.innerMiddle c b)) : a.val b.val=b.val := by
  have he : a*E.nativeMiddle b=E.nativeMiddle b*a := c.middle_injective (by
    simpa only [map_mul,innerMiddle,MonoidHom.comp_apply] using h.eq)
  have he' : a.val*MulAut.conj b.val=MulAut.conj b.val*a.val := congrArg Subtype.val he
  apply hi
  rw [←aut_conj,he',mul_inv_cancel_right]

/-- Local normalization transfers conjugation by every rotation power on a
native Cartan set. The power relation is needed only in the native group. -/
theorem rotation_defect_fixes_cartan
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (s : P₀) (t : P₁) (C : Set B)
    (hC : ∀ b∈C, b∈P₀ ⊓ P₁)
    (hsC : ∀ b∈C, s.val*b*s.val⁻¹∈C)
    (htC : ∀ b∈C, t.val*b*t.val⁻¹∈C)
    (n : ℕ) (hn : (t.val*s.val)^n=1)
    (a : E.middle) (ha : c.middle a=E.nativeRotation c s t^n) :
    ∀ b∈C, a.val b=b := by
  let r := t.val*s.val
  let R := E.nativeRotation c s t
  have hclosed (b : B) (hb : b∈C) : r*b*r⁻¹∈C := by
    have hh := htC _ (hsC b hb)
    convert hh using 1
    dsimp [r]
    group
  let f : C → C := fun b => ⟨r*b.val*r⁻¹,hclosed b.val b.property⟩
  let j : C → M := fun b => E.innerMiddle c ⟨b.val,hC b.val b.property⟩
  have hstep (b : C) : R*j b*R⁻¹=j (f b) := by
    let b₀ : (P₀ ⊓ P₁ : Subgroup B) := ⟨b.val,hC b.val b.property⟩
    let b₁ : (P₀ ⊓ P₁ : Subgroup B) := ⟨s.val*b.val*s.val⁻¹,hC _ (hsC b.val b.property)⟩
    let b₂ : (P₀ ⊓ P₁ : Subgroup B) := ⟨r*b.val*r⁻¹,hC _ (hclosed b.val b.property)⟩
    have hl : E.innerLeft c s*E.innerMiddle c b₀*(E.innerLeft c s)⁻¹=E.innerMiddle c b₁ := by
      rw [E.innerMiddle_left,E.innerMiddle_left,←map_inv,←map_mul,←map_mul]
      rfl
    have hr : E.innerRight c t*E.innerMiddle c b₁*(E.innerRight c t)⁻¹=E.innerMiddle c b₂ := by
      rw [E.innerMiddle_right,E.innerMiddle_right,←map_inv,←map_mul,←map_mul]
      apply congrArg (E.innerRight c)
      apply Subtype.ext
      dsimp [b₁,b₂,r]
      group
    change (E.innerRight c t*E.innerLeft c s)*E.innerMiddle c b₀*
      (E.innerRight c t*E.innerLeft c s)⁻¹=E.innerMiddle c b₂
    calc
      _ = E.innerRight c t*(E.innerLeft c s*E.innerMiddle c b₀*(E.innerLeft c s)⁻¹)*
        (E.innerRight c t)⁻¹ := by group
      _ = _ := by rw [hl,hr]
  have hiter (k : ℕ) (b : C) :
      R^k*j b*(R^k)⁻¹=j ((f^[k]) b) ∧ ((f^[k]) b).val=r^k*b.val*(r^k)⁻¹ := by
    induction k with
    | zero => simp [j]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      constructor
      · rw [pow_succ']
        calc
          _ = R*(R^k*j b*(R^k)⁻¹)*R⁻¹ := by group
          _ = _ := by rw [ih.1,hstep]
      · change r*((f^[k]) b).val*r⁻¹=_
        rw [ih.2,pow_succ']
        group
  intro b hb
  let x : C := ⟨b,hb⟩
  have hx : (f^[n]) x=x := by
    apply Subtype.ext
    simpa only [r,hn,one_mul,inv_one,mul_one] using (hiter n x).2
  have he := (hiter n x).1
  rw [hx] at he
  apply E.middle_fixed_of_commute c hi a ⟨b,hC b hb⟩
  rw [ha]
  exact mul_inv_eq_iff_eq_mul.mp he
/-- The actual constraints on an outer defect after apartment closure.
Triviality of such an automorphism is a separate native rigidity problem. -/
structure CartanFixedInvolution (s : P₀) (t : P₁) (C : Set B) (a : MulAut B) : Prop where
  square : a^2=1
  preserves_left : ∀ b, a b∈P₀ ↔ b∈P₀
  preserves_right : ∀ b, a b∈P₁ ↔ b∈P₁
  fixes_point : a s.val=s.val
  fixes_plane : a t.val=t.val
  fixes_cartan : ∀ b∈C, a b=b

/-- Assemble the local constraints with no rigidity or recognition premise. -/
theorem rotation_defect_constraints
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (s : P₀) (t : P₁) (hs : s^2=1) (ht : t^2=1)
    (C : Set B) (hC : ∀ b∈C, b∈P₀ ⊓ P₁)
    (hsC : ∀ b∈C, s.val*b*s.val⁻¹∈C)
    (htC : ∀ b∈C, t.val*b*t.val⁻¹∈C)
    (n : ℕ) (hn : (t.val*s.val)^n=1)
    (a : E.middle) (ha : c.middle a=E.nativeRotation c s t^n)
    (ha2 : a^2=1) : CartanFixedInvolution s t C a.val := by
  obtain ⟨hsfix,htfix⟩ := E.rotation_defect_fixes_reflections c hi s t hs ht n a ha ha2
  exact ⟨congrArg Subtype.val ha2,E.middle_preserves_left hi a,
    E.middle_preserves_right hi a,hsfix,htfix,
    E.rotation_defect_fixes_cartan c hi s t C hC hsC htC n hn a ha⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.SourceExtension
