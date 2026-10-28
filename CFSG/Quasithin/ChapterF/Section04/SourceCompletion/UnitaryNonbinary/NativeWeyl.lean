module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Inner
import Mathlib.Tactic.Group

/-!
# Native and outer defects of marked unitary rotations

The two native reflections invert every power of their product. If such
a power belongs to the native overlap, faithful endpoint maps transfer
these identities to the base group; its representative commutes with the
native rotation. The concrete unitary centralizer calculations can then
kill it. For a power in the full overlap, the same inversion identity only
puts its square in the native overlap: an outer involution can remain.

This distinguishes the two localization steps needed for the direct Cartan
route of Aschbacher–Smith F.4.10,16–17, pp.279,282–283. The full middle
retains all outer factors. No apartment closure, Weyl relation or native
group identification is assumed in SourceExtension or proved here.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.SourceExtension
open Subgroup Theory.GroupTheory
variable {B : Type*} [Group B] {P₀ P₁ : Subgroup B}
variable (E : SourceExtension P₀ P₁) {M : Type*} [Group M]
variable (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))

def nativeMiddle : (P₀ ⊓ P₁ : Subgroup B) →* E.middle :=
  (MulAut.conj.comp (P₀ ⊓ P₁ : Subgroup B).subtype).codRestrict _ (fun b =>
    ⟨(E.nativeLeft ⟨b,b.property.1⟩).property,(E.nativeRight ⟨b,b.property.2⟩).property⟩)

def innerMiddle : (P₀ ⊓ P₁ : Subgroup B) →* M := c.middle.comp E.nativeMiddle

theorem innerMiddle_left (b : (P₀ ⊓ P₁ : Subgroup B)) :
    E.innerMiddle c b = E.innerLeft c ⟨b,b.property.1⟩ := rfl

theorem innerMiddle_right (b : (P₀ ⊓ P₁ : Subgroup B)) :
    E.innerMiddle c b = E.innerRight c ⟨b,b.property.2⟩ :=
  DFunLike.congr_fun c.compatible (E.nativeMiddle b)

theorem innerLeft_injective (hi : Function.Injective (MulAut.conj : B →* MulAut B)) :
    Function.Injective (E.innerLeft c) := by
  intro x y he
  apply Subtype.ext
  apply hi
  exact congrArg Subtype.val (c.left_injective he)

theorem innerRight_injective (hi : Function.Injective (MulAut.conj : B →* MulAut B)) :
    Function.Injective (E.innerRight c) := by
  intro x y he
  apply Subtype.ext
  apply hi
  exact congrArg Subtype.val (c.right_injective he)

def nativeRotation (s : P₀) (t : P₁) : M := E.innerRight c t * E.innerLeft c s

private theorem involution_inverts_rotation_power {A : Type*} [Group A]
    (s t : A) (hs : s^2=1) (ht : t^2=1) (n : ℕ) :
    s * (t*s)^n * s⁻¹ = ((t*s)^n)⁻¹ ∧
      t * (t*s)^n * t⁻¹ = ((t*s)^n)⁻¹ := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs)
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht)
  have hl : s * (t*s) * s⁻¹ = (t*s)⁻¹ := by
    rw [←mul_assoc s t s,mul_inv_cancel_right,_root_.mul_inv_rev,hsi,hti]
  have hr : t * (t*s) * t⁻¹ = (t*s)⁻¹ := by
    rw [←mul_assoc t t s,←pow_two,ht,one_mul,_root_.mul_inv_rev,hsi]
  constructor
  · rw [←conj_pow,hl,inv_pow]
  · rw [←conj_pow,hr,inv_pow]

/-- If a rotation-power defect is represented in the native overlap, then its
native representative commutes with the actual native quarter-turn. -/
theorem nativeRotation_power_defect_commutes
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (s : P₀) (t : P₁) (hs : s^2=1) (ht : t^2=1)
    (n : ℕ) (b : (P₀ ⊓ P₁ : Subgroup B))
    (hb : E.nativeRotation c s t ^ n = E.innerMiddle c b) :
    Commute b.val (t.val*s.val) := by
  have hs' : (E.innerLeft c s)^2=1 := by rw [←map_pow,hs,map_one]
  have ht' : (E.innerRight c t)^2=1 := by rw [←map_pow,ht,map_one]
  obtain ⟨hL,hR⟩ := involution_inverts_rotation_power (E.innerLeft c s) (E.innerRight c t) hs' ht' n
  change E.innerLeft c s * E.nativeRotation c s t ^ n * (E.innerLeft c s)⁻¹ =
    (E.nativeRotation c s t ^ n)⁻¹ at hL
  change E.innerRight c t * E.nativeRotation c s t ^ n * (E.innerRight c t)⁻¹ =
    (E.nativeRotation c s t ^ n)⁻¹ at hR
  rw [hb,E.innerMiddle_left] at hL
  rw [hb,E.innerMiddle_right] at hR
  have hsLocal : s * ⟨b,b.property.1⟩ * s⁻¹ = (⟨b,b.property.1⟩ : P₀)⁻¹ :=
    E.innerLeft_injective c hi (by simpa only [map_mul,map_inv] using hL)
  have htLocal : t * ⟨b,b.property.2⟩ * t⁻¹ = (⟨b,b.property.2⟩ : P₁)⁻¹ :=
    E.innerRight_injective c hi (by simpa only [map_mul,map_inv] using hR)
  have hsB : s.val*b.val*s.val⁻¹=b.val⁻¹ := congrArg Subtype.val hsLocal
  have htB : t.val*b.val*t.val⁻¹=b.val⁻¹ := congrArg Subtype.val htLocal
  have he : (t.val*s.val)*b.val*(t.val*s.val)⁻¹=b.val := by
    calc
      _ = t.val*(s.val*b.val*s.val⁻¹)*t.val⁻¹ := by group
      _ = t.val*b.val⁻¹*t.val⁻¹ := by rw [hsB]
      _ = (t.val*b.val*t.val⁻¹)⁻¹ := by group
      _ = b.val := by rw [htB,inv_inv]
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The precise algebraic use of a native overlap-centralizer calculation.
The localization premise concerns the native image, not the full middle. -/
theorem nativeRotation_power_eq_one_of_native_overlap
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (s : P₀) (t : P₁) (hs : s^2=1) (ht : t^2=1)
    (hfix : ∀ b : (P₀ ⊓ P₁ : Subgroup B), Commute b.val (t.val*s.val) → b.val=1)
    (n : ℕ) (hb : E.nativeRotation c s t ^ n ∈ (E.innerMiddle c).range) :
    E.nativeRotation c s t ^ n = 1 := by
  obtain ⟨b,hb⟩ := hb
  have he : b=1 := Subtype.ext (hfix b (E.nativeRotation_power_defect_commutes c hi s t hs ht n b hb.symm))
  rw [←hb,he,map_one]

/-- Inversion by one native reflection makes the square of a full-overlap
rotation defect inner. No oddness of the full extension is assumed. -/
theorem nativeRotation_power_sq_mem_innerMiddle
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (s : P₀) (t : P₁) (hs : s^2=1) (ht : t^2=1)
    (n : ℕ) (hb : E.nativeRotation c s t ^ n ∈ c.middle.range) :
    (E.nativeRotation c s t ^ n)^2 ∈ (E.innerMiddle c).range := by
  obtain ⟨a,ha⟩ := hb
  have hs' : (E.innerLeft c s)^2=1 := by rw [←map_pow,hs,map_one]
  have ht' : (E.innerRight c t)^2=1 := by rw [←map_pow,ht,map_one]
  have hL := (involution_inverts_rotation_power (E.innerLeft c s)
    (E.innerRight c t) hs' ht' n).1
  change E.innerLeft c s * E.nativeRotation c s t ^ n * (E.innerLeft c s)⁻¹ =
    (E.nativeRotation c s t ^ n)⁻¹ at hL
  rw [←ha] at hL
  have hl : E.nativeLeft s * E.amalgam.left a * (E.nativeLeft s)⁻¹ =
      (E.amalgam.left a)⁻¹ := c.left_injective (by
        simpa only [map_mul,map_inv,innerLeft,RankTwoAmalgam.FaithfulCompletion.middle,
          MonoidHom.comp_apply] using hL)
  have hl' : MulAut.conj s.val * a.val * (MulAut.conj s.val)⁻¹ = a.val⁻¹ :=
    congrArg Subtype.val hl
  have hn : a.val * MulAut.conj s.val * a.val⁻¹ = MulAut.conj (a.val s.val) := by
    ext x
    simp [MulAut.conj_apply]
  have hm : a.val * MulAut.conj s.val * a.val = MulAut.conj s.val := by
    apply mul_right_cancel (b := (MulAut.conj s.val)⁻¹)
    calc
      _ = a.val * (MulAut.conj s.val * a.val * (MulAut.conj s.val)⁻¹) := by group
      _ = 1 := by rw [hl',mul_inv_cancel]
      _ = _ := (mul_inv_cancel _).symm
  let b : B := (a.val s.val)⁻¹ * s.val
  have ha2 : a.val^2 = MulAut.conj b := by
    calc
      _ = (MulAut.conj (a.val s.val))⁻¹ * (a.val * MulAut.conj s.val * a.val) := by
        rw [←hn,pow_two]
        group
      _ = _ := by rw [hm]; simp only [b,map_mul,map_inv]
  have hbm : MulAut.conj b ∈ E.middle := ha2 ▸ E.middle.pow_mem a.property 2
  have hb : b ∈ P₀ ⊓ P₁ := (mem_map_iff_mem hi).mp
    ((E.middle_inner hi).le ⟨hbm,⟨b,rfl⟩⟩)
  have he : E.nativeMiddle ⟨b,hb⟩ = a^2 := Subtype.ext ha2.symm
  refine ⟨⟨b,hb⟩,?_⟩
  change c.middle (E.nativeMiddle ⟨b,hb⟩) = _
  rw [he,map_pow,ha]

/-- Native centralizer control leaves at most an involutory defect in the
full overlap; the extension's even degree has not been discarded. -/
theorem nativeRotation_power_sq_eq_one_of_middle
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (s : P₀) (t : P₁) (hs : s^2=1) (ht : t^2=1)
    (hfix : ∀ b : (P₀ ⊓ P₁ : Subgroup B), Commute b.val (t.val*s.val) → b.val=1)
    (n : ℕ) (hb : E.nativeRotation c s t ^ n ∈ c.middle.range) :
    (E.nativeRotation c s t ^ n)^2 = 1 := by
  have he := E.nativeRotation_power_sq_mem_innerMiddle c hi s t hs ht n hb
  rw [←pow_mul] at he ⊢
  exact E.nativeRotation_power_eq_one_of_native_overlap c hi s t hs ht hfix (n*2) he
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.SourceExtension
