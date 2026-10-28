module

public import Theory.GroupTheory.Amalgam.MixedDihedralEight.Fiber
public import Theory.GroupTheory.Amalgam.SylowRigidity
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# The two mixed amalgams over a dihedral group of order eight

The good vertex is the square action in S₄. The bad vertex is the cubic
fiber product selected by an index-two character on D₈. There are four
characters: the trivial character, reflection parity, rotation parity,
and permutation sign. Faithfulness excludes the first and last, leaving
precisely the two mixed rows at overlap order eight.

Source: Aschbacher–Smith F.6.5(2)(iii–iv), printed p.305.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.RankTwoAmalgam.MixedEight
abbrev D8 := DihedralGroup 4
abbrev S4 := Equiv.Perm (Fin 4)

def squareWord : D8 → S4
  | .r i => finRotate 4 ^ i.val
  | .sr i => Equiv.swap 1 3 * finRotate 4 ^ i.val

def square : D8 →* S4 where
  toFun := squareWord
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem square_injective : Function.Injective square := by decide +kernel

noncomputable def squareSylow : Sylow 2 S4 := Sylow.ofCard square.range (by
  rw [← Nat.card_congr (MonoidHom.ofInjective square_injective).toEquiv]
  norm_num [Nat.card_eq_fintype_card, DihedralGroup.card, Fintype.card_perm, Nat.factorial]
  decide +kernel)

def rotationWord : D8 → ℤˣ
  | .r i => (-1) ^ i.val
  | .sr i => (-1) ^ i.val
def reflectionWord : D8 → ℤˣ
  | .r _ => 1
  | .sr _ => -1

def rotationCharacter : D8 →* ℤˣ where
  toFun := rotationWord
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def reflectionCharacter : D8 →* ℤˣ where
  toFun := reflectionWord
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def signCharacter : D8 →* ℤˣ := Equiv.Perm.sign.comp square

private theorem character_ext {χ ψ : D8 →* ℤˣ}
    (hr : χ (.r 1) = ψ (.r 1)) (hs : χ (.sr 0) = ψ (.sr 0)) : χ = ψ := by
  ext x
  rcases x with i | i
  · have he : (DihedralGroup.r i : D8) = (.r 1) ^ i.val := by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    rw [he, map_pow, map_pow, hr]
  · have he : (DihedralGroup.sr i : D8) = .sr 0 * (.r 1) ^ i.val := by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val, DihedralGroup.sr_mul_r, zero_add]
    rw [he, map_mul, map_mul, map_pow, map_pow, hr, hs]

theorem character_cases (χ : D8 →* ℤˣ) :
    χ = 1 ∨ χ = reflectionCharacter ∨ χ = rotationCharacter ∨ χ = signCharacter := by
  rcases Int.units_eq_one_or (χ (.r 1)) with hr | hr
  · rcases Int.units_eq_one_or (χ (.sr 0)) with hs | hs
    · exact Or.inl (character_ext hr hs)
    · exact Or.inr (Or.inl (character_ext hr hs))
  · rcases Int.units_eq_one_or (χ (.sr 0)) with hs | hs
    · exact Or.inr (Or.inr (Or.inl (character_ext hr hs)))
    · exact Or.inr (Or.inr (Or.inr (character_ext hr hs)))

def amalgam (χ : D8 →* ℤˣ) : RankTwoAmalgam S4 D8 (CubicFiber.group χ) :=
  ⟨square, CubicFiber.inclusion χ⟩

private theorem fiber_kernel_normal (χ : D8 →* ℤˣ) :
    (χ.ker.map (CubicFiber.inclusion χ)).Normal := by
  let f : CubicFiber.group χ →* CubicFiber.S3 :=
    (MonoidHom.snd _ _).comp (CubicFiber.group χ).subtype
  have he : χ.ker.map (CubicFiber.inclusion χ) = f.ker := by
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      change CubicFiber.reflection (χ d) = 1
      rw [show χ d = 1 from hd, map_one]
    · intro hx
      have hs : x.val.2 = 1 := hx
      have hc : χ x.val.1 = 1 := x.property.trans (by change Equiv.Perm.sign x.val.2 = 1; rw [hs, map_one])
      refine ⟨x.val.1, hc, ?_⟩
      apply Subtype.ext
      exact Prod.ext rfl (by change CubicFiber.reflection (χ x.val.1) = x.val.2; rw [hc, hs, map_one])
  rw [he]
  infer_instance

private theorem sign_kernel_normal : (signCharacter.ker.map square).Normal := by
  have cert : ∀ (g : S4) (d : D8), signCharacter d = 1 →
      ∃ e : D8, signCharacter e = 1 ∧ square e = g * square d * g⁻¹ := by decide +kernel
  constructor
  rintro x ⟨d, hd, rfl⟩ g
  obtain ⟨e, he, hge⟩ := cert g d hd
  exact ⟨e, he, hge⟩

/-- The source faithfulness condition removes exactly the normal-four kernel. -/
theorem character_cases_of_faithful (χ : D8 →* ℤˣ)
    (hne : χ ≠ 1) (hf : Faithful (amalgam χ)) :
    χ = reflectionCharacter ∨ χ = rotationCharacter := by
  rcases character_cases χ with h | h | h | h
  · exact (hne h).elim
  · exact Or.inl h
  · exact Or.inr h
  · subst χ
    have hh := hf signCharacter.ker sign_kernel_normal (fiber_kernel_normal signCharacter)
    have hm : (DihedralGroup.r 2 : D8) ∈ signCharacter.ker := by decide +kernel
    rw [hh] at hm
    exact (by decide : (DihedralGroup.r 2 : D8) ≠ 1) hm |>.elim

end Theory.GroupTheory.RankTwoAmalgam.MixedEight
