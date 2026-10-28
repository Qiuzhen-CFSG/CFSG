module

public import Theory.GroupTheory.Amalgam.MixedDihedralEight.Models

/-!
# The mixed amalgam over C₂ × D₈

The character defining a cubic fiber product over C₂ × D₈ must be nontrivial
on the central C₂ in a faithful amalgam. The normal four-group in S₄ removes
two of the four remaining characters. Multiplying the central coordinate by
permutation sign interchanges the two surviving characters. This gives one
amalgam, with vertices C₂ × S₄ and S₃ × D₈, and retains both structure maps.

Source: Aschbacher–Smith F.6.5(2)(v), printed p.305.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.RankTwoAmalgam.MixedSixteen

abbrev Middle := ℤˣ × MixedEight.D8
abbrev Left := ℤˣ × MixedEight.S4

def left : Middle →* Left :=
  (MonoidHom.fst _ _).prod (MixedEight.square.comp (MonoidHom.snd _ _))

theorem left_injective : Function.Injective left := by
  intro x y he
  exact Prod.ext (congrArg (fun z : Left => z.1) he)
    (MixedEight.square_injective (congrArg (fun z : Left => z.2) he))

noncomputable def leftSylow : Sylow 2 Left := Sylow.ofCard left.range (by
  rw [← Nat.card_congr (MonoidHom.ofInjective left_injective).toEquiv]
  norm_num [Nat.card_eq_fintype_card, DihedralGroup.card, Fintype.card_perm, Nat.factorial]
  decide +kernel)

theorem leftSylow_coe : (leftSylow : Subgroup Left) = left.range := rfl

def amalgam (χ : Middle →* ℤˣ) : RankTwoAmalgam Left Middle (CubicFiber.group χ) :=
  ⟨left, CubicFiber.inclusion χ⟩

def character (ψ : MixedEight.D8 →* ℤˣ) : Middle →* ℤˣ :=
  (MonoidHom.fst _ _) * ψ.comp (MonoidHom.snd _ _)

private theorem fiber_normal {B : Type*} [Group B]
    (χ : B →* ℤˣ) (N : Subgroup B) [N.Normal] (hN : N ≤ χ.ker) :
    (N.map (CubicFiber.inclusion χ)).Normal := by
  constructor
  rintro x ⟨b, hb, rfl⟩ g
  refine ⟨g.val.1 * b * g.val.1⁻¹, (inferInstance : N.Normal).conj_mem b hb g.val.1, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change CubicFiber.reflection (χ (g.val.1 * b * g.val.1⁻¹)) =
      g.val.2 * CubicFiber.reflection (χ b) * g.val.2⁻¹
    have hbχ : χ b = 1 := hN hb
    have hc : χ (g.val.1 * b * g.val.1⁻¹) = 1 := by
      simp only [map_mul, map_inv, hbχ, mul_one, mul_inv_cancel]
    rw [hc, hbχ, map_one, mul_one, mul_inv_cancel]

private theorem central_character_of_faithful (χ : Middle →* ℤˣ)
    (hf : Faithful (amalgam χ)) : χ (-1, 1) = -1 := by
  rcases Int.units_eq_one_or (χ (-1, 1)) with h | h
  · let N : Subgroup Middle := (MonoidHom.snd _ _).ker
    have hN : N ≤ χ.ker := by
      rintro ⟨ε,d⟩ hd
      change d = 1 at hd
      subst d
      rcases Int.units_eq_one_or ε with he | he
      · subst ε; exact map_one χ
      · subst ε; exact h
    have hleft : (N.map left).Normal := by
      have he : N.map left = (MonoidHom.snd ℤˣ MixedEight.S4).ker := by
        ext x
        constructor
        · rintro ⟨b, hb, rfl⟩
          change MixedEight.square b.2 = 1
          rw [show b.2 = 1 from hb, map_one]
        · intro hx
          refine ⟨(x.1,1), rfl, ?_⟩
          exact Prod.ext rfl ((map_one MixedEight.square).trans (show x.2 = 1 from hx).symm)
      rw [he]
      infer_instance
    have hbot := hf N hleft (fiber_normal χ N hN)
    have hm : (-1, 1) ∈ N := rfl
    rw [hbot] at hm
    exact (by decide : ((-1, 1) : Middle) ≠ 1) hm |>.elim
  · exact h

private theorem character_decomposition (χ : Middle →* ℤˣ)
    (hc : χ (-1, 1) = -1) :
    χ = character (χ.comp (MonoidHom.inr ℤˣ MixedEight.D8)) := by
  apply MonoidHom.ext
  rintro ⟨ε,d⟩
  have hε : χ (ε, 1) = ε := by
    rcases Int.units_eq_one_or ε with he | he
    · subst ε; exact map_one χ
    · subst ε; exact hc
  calc
    χ (ε,d) = χ ((ε,1) * (1,d)) := by simp
    _ = χ (ε,1) * χ (1,d) := map_mul χ _ _
    _ = character (χ.comp (MonoidHom.inr ℤˣ MixedEight.D8)) (ε,d) := by rw [hε]; rfl

private theorem sign_four_image_normal :
    (((⊥ : Subgroup ℤˣ).prod MixedEight.signCharacter.ker).map left).Normal := by
  have cert : ∀ (g : MixedEight.S4) (d : MixedEight.D8), MixedEight.signCharacter d = 1 →
      ∃ e : MixedEight.D8, MixedEight.signCharacter e = 1 ∧
        MixedEight.square e = g * MixedEight.square d * g⁻¹ := by decide +kernel
  constructor
  rintro x ⟨⟨ε,d⟩, hd, rfl⟩ ⟨η,g⟩
  change ε = 1 ∧ MixedEight.signCharacter d = 1 at hd
  obtain ⟨e, he, hge⟩ := cert g d hd.2
  refine ⟨(1,e), ⟨rfl,he⟩, ?_⟩
  apply Prod.ext
  · change 1 = η * ε * η⁻¹
    rw [hd.1, mul_one, mul_inv_cancel]
  · exact hge

private theorem exclude_character (ψ : MixedEight.D8 →* ℤˣ)
    (hψ : ψ = 1 ∨ ψ = MixedEight.signCharacter)
    (hf : Faithful (amalgam (character ψ))) : False := by
  let N := (⊥ : Subgroup ℤˣ).prod MixedEight.signCharacter.ker
  have hN : N ≤ (character ψ).ker := by
    rintro ⟨ε,d⟩ hd
    change ε = 1 ∧ MixedEight.signCharacter d = 1 at hd
    change ε * ψ d = 1
    rcases hψ with h | h
    · rw [hd.1, h]; rfl
    · rw [hd.1, h, hd.2, one_mul]
  have hbot := hf N sign_four_image_normal (fiber_normal (character ψ) N hN)
  have hm : ((1, DihedralGroup.r 2) : Middle) ∈ N := by
    change (1 : ℤˣ) = 1 ∧ MixedEight.signCharacter (DihedralGroup.r 2) = 1
    decide +kernel
  rw [hbot] at hm
  exact (by decide : ((1, DihedralGroup.r 2) : Middle) ≠ 1) hm

/-- Faithfulness leaves the two characters related by the S₄ sign shear. -/
theorem character_cases_of_faithful (χ : Middle →* ℤˣ)
    (hf : Faithful (amalgam χ)) :
    χ = character MixedEight.reflectionCharacter ∨ χ = character MixedEight.rotationCharacter := by
  let ψ := χ.comp (MonoidHom.inr ℤˣ MixedEight.D8)
  have hχ : χ = character ψ := character_decomposition χ (central_character_of_faithful χ hf)
  rw [hχ] at hf ⊢
  rcases MixedEight.character_cases ψ with h | h | h | h
  · exact (exclude_character ψ (Or.inl h) hf).elim
  · exact Or.inl (congrArg character h)
  · exact Or.inr (congrArg character h)
  · exact (exclude_character ψ (Or.inr h) hf).elim

/-- Multiplying the central coordinate by a character is an involutory automorphism. -/
def shear {A : Type*} [Group A] (ψ : A →* ℤˣ) : MulAut (ℤˣ × A) where
  toFun x := (x.1 * ψ x.2, x.2)
  invFun x := (x.1 * ψ x.2, x.2)
  left_inv x := by
    apply Prod.ext
    · change (x.1 * ψ x.2) * ψ x.2 = x.1
      have hs : ∀ ε : ℤˣ, ε * ε = 1 := by decide +kernel
      rw [mul_assoc, hs, mul_one]
    · rfl
  right_inv x := by
    apply Prod.ext
    · change (x.1 * ψ x.2) * ψ x.2 = x.1
      have hs : ∀ ε : ℤˣ, ε * ε = 1 := by decide +kernel
      rw [mul_assoc, hs, mul_one]
    · rfl
  map_mul' x y := by
    apply Prod.ext
    · change (x.1 * y.1) * ψ (x.2 * y.2) = (x.1 * ψ x.2) * (y.1 * ψ y.2)
      rw [map_mul]
      ac_rfl
    · rfl

private theorem rotation_shear : ∀ b : Middle,
    character MixedEight.rotationCharacter (shear MixedEight.signCharacter b) =
      character MixedEight.reflectionCharacter b := by decide +kernel

private theorem reflection_shear : ∀ b : Middle,
    character MixedEight.reflectionCharacter (shear MixedEight.signCharacter b) =
      character MixedEight.rotationCharacter b := by decide +kernel

/-- The sign shear transports the two cubic fiber products. -/
def fiberShear : CubicFiber.group (character MixedEight.reflectionCharacter) ≃*
    CubicFiber.group (character MixedEight.rotationCharacter) where
  toFun x := ⟨(shear MixedEight.signCharacter x.val.1, x.val.2), by
    change character MixedEight.rotationCharacter (shear MixedEight.signCharacter x.val.1) = _
    rw [rotation_shear]
    exact x.property⟩
  invFun x := ⟨(shear MixedEight.signCharacter x.val.1, x.val.2), by
    change character MixedEight.reflectionCharacter (shear MixedEight.signCharacter x.val.1) = _
    rw [reflection_shear]
    exact x.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact (shear MixedEight.signCharacter).left_inv x.val.1
    · rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact (shear MixedEight.signCharacter).right_inv x.val.1
    · rfl
  map_mul' x y := by
    apply Subtype.ext
    exact Prod.ext ((shear MixedEight.signCharacter).map_mul x.val.1 y.val.1) rfl

/-- Both maps of the surviving character amalgams commute with the sign shear. -/
def reflectionRotationIso :
    Iso (amalgam (character MixedEight.reflectionCharacter))
      (amalgam (character MixedEight.rotationCharacter)) where
  left := shear Equiv.Perm.sign
  middle := shear MixedEight.signCharacter
  right := fiberShear
  left_commutes b := rfl
  right_commutes b := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg CubicFiber.reflection (rotation_shear b).symm

/-- Eliminating the central coordinate identifies a cubic fiber vertex with S₃ × D₈. -/
def vertexEquiv (ψ : MixedEight.D8 →* ℤˣ) :
    CubicFiber.group (character ψ) ≃* (CubicFiber.S3 × MixedEight.D8) where
  toFun x := (x.val.2, x.val.1.2)
  invFun x := ⟨((Equiv.Perm.sign x.1 * (ψ x.2)⁻¹, x.2), x.1), by
    change (Equiv.Perm.sign x.1 * (ψ x.2)⁻¹) * ψ x.2 = Equiv.Perm.sign x.1
    exact inv_mul_cancel_right _ _⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · change Equiv.Perm.sign x.val.2 * (ψ x.val.1.2)⁻¹ = x.val.1.1
        have hx : x.val.1.1 * ψ x.val.1.2 = Equiv.Perm.sign x.val.2 := x.property
        rw [← hx, mul_inv_cancel_right]
      · rfl
    · rfl
  right_inv x := rfl
  map_mul' x y := rfl

theorem vertexEquiv_inclusion (ψ : MixedEight.D8 →* ℤˣ) (b : Middle) :
    vertexEquiv ψ (CubicFiber.inclusion (character ψ) b) =
      (CubicFiber.reflection (b.1 * ψ b.2), b.2) := rfl

/-- The row (v) model, including the exact two overlap embeddings. -/
def standard : RankTwoAmalgam Left Middle (CubicFiber.S3 × MixedEight.D8) where
  left := left
  right := (CubicFiber.reflection.comp (character MixedEight.rotationCharacter)).prod
    (MonoidHom.snd _ _)

/-- The canonical cubic fiber model is the concrete row (v) amalgam. -/
def canonicalIso : Iso (amalgam (character MixedEight.rotationCharacter)) standard where
  left := MulEquiv.refl _
  middle := MulEquiv.refl _
  right := vertexEquiv MixedEight.rotationCharacter
  left_commutes _ := rfl
  right_commutes _ := rfl

/-- Every faithful marked mixed amalgam over C₂ × D₈ is the row (v) model. -/
theorem iso_standard_of_faithful (χ : Middle →* ℤˣ) (hf : Faithful (amalgam χ)) :
    Nonempty (Iso (amalgam χ) standard) := by
  rcases character_cases_of_faithful χ hf with h | h
  · subst χ
    exact ⟨reflectionRotationIso.trans canonicalIso⟩
  · subst χ
    exact ⟨canonicalIso⟩

end Theory.GroupTheory.RankTwoAmalgam.MixedSixteen
