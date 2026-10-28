module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.BlockConstruction.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Recognition of the faithful binary plane action

After choosing a basis, a faithful binary plane representation embeds into
SL₂(2): every invertible binary determinant is one. Two distinct nonidentity
involutions generate all six matrices, so the embedding is surjective. The
result retains the actual coordinate equivalence and its action formula.

This is the model identification in Kurzweil–Stellmacher 9.3.3, printed
pp.241–242 of `refs/original/kurzweil.pdf`.
-/

public section

open Matrix
namespace CFSG.Quasithin.ChapterB.Glauberman.BlockConstruction.PairRecognition
private abbrev SL := SpecialLinearGroup (Fin 2) (ZMod 2)
private lemma binary_unit (a b : ZMod 2) (hab : a * b = 1) : a = 1 := by
  have h : ∀ a b : ZMod 2, a * b = 1 → a = 1 := by decide +kernel
  exact h a b hab

lemma sl_card : Nat.card (SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private lemma sl_six_words : ∀ a b c : SL,
    a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b →
    c = 1 ∨ c = a ∨ c = b ∨ c = a * b ∨ c = b * a ∨ c = a * b * a := by
  decide +kernel

variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

lemma exists_natural_model (σ : Representation (ZMod 2) H W) (hf : Function.Injective σ)
    (hd : Module.finrank (ZMod 2) W = 2) (t u : H)
    (ht : t * t = 1) (hu : u * u = 1) (htn : t ≠ 1) (hun : u ≠ 1) (htu : t ≠ u) :
    ∃ e : H ≃* SpecialLinearGroup (Fin 2) (ZMod 2),
      ∃ f : W ≃ₗ[ZMod 2] (Fin 2 → ZMod 2),
        ∀ g w, f (σ g w) = Representation.specialLinearNatural 2 (e g) (f w) := by
  classical
  let b := Module.finBasisOfFinrankEq (ZMod 2) W hd
  let m := LinearMap.toMatrixAlgEquiv b
  have hdet (g : H) : (m (σ g)).det = 1 := by
    apply binary_unit _ (m (σ g⁻¹)).det
    rw [← Matrix.det_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, Matrix.det_one]
  let f : H →* SL := {
    toFun g := ⟨m (σ g), hdet g⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' g h := by
      apply Subtype.ext
      change m (σ (g * h)) = m (σ g) * m (σ h)
      rw [map_mul, map_mul] }
  have hfi : Function.Injective f := by
    intro g h he
    apply hf
    apply m.injective
    exact congrArg Subtype.val he
  have hfs : Function.Surjective f := by
    intro c
    have hft : f t * f t = 1 := by rw [← map_mul, ht, map_one]
    have hfu : f u * f u = 1 := by rw [← map_mul, hu, map_one]
    have hftn : f t ≠ 1 := fun he => htn (hfi (he.trans (map_one f).symm))
    have hfun : f u ≠ 1 := fun he => hun (hfi (he.trans (map_one f).symm))
    have hftu : f t ≠ f u := fun he => htu (hfi he)
    rcases sl_six_words (f t) (f u) c ⟨hft, hfu, hftn, hfun, hftu⟩ with
      he | he | he | he | he | he
    · exact ⟨1, by simpa using he.symm⟩
    · exact ⟨t, he.symm⟩
    · exact ⟨u, he.symm⟩
    · exact ⟨t * u, by simpa using he.symm⟩
    · exact ⟨u * t, by simpa using he.symm⟩
    · exact ⟨t * u * t, by simpa using he.symm⟩
  refine ⟨MulEquiv.ofBijective f ⟨hfi, hfs⟩, b.equivFun, ?_⟩
  intro g w
  exact (LinearMap.toMatrix_mulVec_repr b b (σ g) w).symm

end CFSG.Quasithin.ChapterB.Glauberman.BlockConstruction.PairRecognition
