module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.ModelDefs

/-!
# Independent sign changes on the two marked cubic directions

An automorphism of C₃ × C₃ preserving each coordinate line acts by a sign
on each line. A group of such automorphisms containing the second-coordinate
inversion and moving the first coordinate has the full elementary-four image.
This is the finite calculation used after the source normalizer has been
shown to preserve the actual marked lines in Aschbacher–Smith 13.8.16(1),
printed p.952 (PDF p.969). It does not assert those geometric premises.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer.Diagonal

def signAut (s : C2) : MulAut Model.C3 where
  toFun x := if s = 1 then x else x⁻¹
  invFun x := if s = 1 then x else x⁻¹
  left_inv x := by split_ifs <;> simp
  right_inv x := by split_ifs <;> simp
  map_mul' x y := by split_ifs <;> simp [mul_comm]

def diagonalAction : E4 →* MulAut Model.CubicPlane where
  toFun s := (signAut (s 0)).prodCongr (signAut (s 1))
  map_one' := by ext x <;> rfl
  map_mul' s t := by
    apply MulEquiv.ext
    intro x
    apply Prod.ext
    · exact (show ∀ (a b : C2) (c : Model.C3),
          signAut (a * b) c = signAut a (signAut b c) by decide) (s 0) (t 0) x.1
    · exact (show ∀ (a b : C2) (c : Model.C3),
          signAut (a * b) c = signAut a (signAut b c) by decide) (s 1) (t 1) x.2

theorem signAut_injective : Function.Injective signAut := by
  intro s t h
  have h1 := DFunLike.congr_fun h (Multiplicative.ofAdd (1 : ZMod 3))
  exact (show ∀ a b : C2,
    signAut a (Multiplicative.ofAdd (1 : ZMod 3)) =
      signAut b (Multiplicative.ofAdd (1 : ZMod 3)) → a = b by decide) s t h1

theorem diagonalAction_injective : Function.Injective diagonalAction := by
  intro s t h
  funext i
  fin_cases i
  · apply signAut_injective
    apply MulEquiv.ext
    intro x
    exact congrArg Prod.fst (DFunLike.congr_fun h (x, 1))
  · apply signAut_injective
    apply MulEquiv.ext
    intro x
    exact congrArg Prod.snd (DFunLike.congr_fun h (1, x))

private theorem cubic_hom_cases : ∀ f : Model.C3 → Model.C3,
    (∀ a b, f (a * b) = f a * f b) → Function.Injective f →
      (∀ x, f x = x) ∨ (∀ x, f x = x⁻¹) := by decide +kernel

theorem exists_diagonal_of_axes (a : MulAut Model.CubicPlane)
    (hs : Model.scalarAxis.map a.toMonoidHom = Model.scalarAxis)
    (hd : Model.derivedAxis.map a.toMonoidHom = Model.derivedAxis) :
    ∃ s : E4, diagonalAction s = a := by
  have hs' (x : Model.C3) : (a (x, 1)).2 = 1 := by
    have h : a (x, 1) ∈ Model.scalarAxis :=
      hs ▸ mem_map_of_mem a.toMonoidHom (show (x, 1) ∈ Model.scalarAxis from ⟨mem_top _, rfl⟩)
    exact h.2
  have hd' (x : Model.C3) : (a (1, x)).1 = 1 := by
    have h : a (1, x) ∈ Model.derivedAxis :=
      hd ▸ mem_map_of_mem a.toMonoidHom (show (1, x) ∈ Model.derivedAxis from ⟨rfl, mem_top _⟩)
    exact h.1
  have hf0 : Function.Injective (fun x : Model.C3 => (a (x, 1)).1) := by
    intro x y h
    have he : a (x, 1) = a (y, 1) := Prod.ext h ((hs' x).trans (hs' y).symm)
    exact congrArg Prod.fst (a.injective he)
  have hf1 : Function.Injective (fun x : Model.C3 => (a (1, x)).2) := by
    intro x y h
    have he : a (1, x) = a (1, y) := Prod.ext ((hd' x).trans (hd' y).symm) h
    exact congrArg Prod.snd (a.injective he)
  have hm0 : ∀ x y : Model.C3, (a (x * y, 1)).1 = (a (x, 1)).1 * (a (y, 1)).1 := by
    intro x y
    exact congrArg Prod.fst (a.map_mul (x, 1) (y, 1))
  have hm1 : ∀ x y : Model.C3, (a (1, x * y)).2 = (a (1, x)).2 * (a (1, y)).2 := by
    intro x y
    exact congrArg Prod.snd (a.map_mul (1, x) (1, y))
  obtain ⟨s, hs0⟩ : ∃ s : C2, ∀ x : Model.C3, signAut s x = (a (x, 1)).1 := by
    rcases cubic_hom_cases _ hm0 hf0 with h | h
    · exact ⟨1, fun x => (h x).symm⟩
    · exact ⟨Multiplicative.ofAdd (1 : ZMod 2), fun x => (h x).symm⟩
  obtain ⟨t, ht1⟩ : ∃ t : C2, ∀ x : Model.C3, signAut t x = (a (1, x)).2 := by
    rcases cubic_hom_cases _ hm1 hf1 with h | h
    · exact ⟨1, fun x => (h x).symm⟩
    · exact ⟨Multiplicative.ofAdd (1 : ZMod 2), fun x => (h x).symm⟩
  refine ⟨![s,t], ?_⟩
  apply MulEquiv.ext
  intro x
  have ha := a.map_mul (x.1, 1) (1, x.2)
  change (signAut s x.1, signAut t x.2) = a x
  rw [hs0, ht1]
  calc
    _ = a (x.1, 1) * a (1, x.2) := by
      apply Prod.ext
      · change (a (x.1, 1)).1 = (a (x.1, 1)).1 * (a (1, x.2)).1
        rw [hd', mul_one]
      · change (a (1, x.2)).2 = (a (x.1, 1)).2 * (a (1, x.2)).2
        rw [hs', one_mul]
    _ = a x := by simpa using ha.symm

noncomputable def diagonalRangeEquiv : diagonalAction.range ≃* E4 :=
  (MulEquiv.ofBijective diagonalAction.rangeRestrict
    ⟨fun _ _ h => diagonalAction_injective (congrArg Subtype.val h),
      diagonalAction.rangeRestrict_surjective⟩).symm

def derivedFlip : E4 := ![1, Multiplicative.ofAdd (1 : ZMod 2)]

theorem range_le_diagonal {A : Type*} [Group A] (ρ : A →* MulAut Model.CubicPlane)
    (hs : ∀ a, Model.scalarAxis.map (ρ a).toMonoidHom = Model.scalarAxis)
    (hd : ∀ a, Model.derivedAxis.map (ρ a).toMonoidHom = Model.derivedAxis) :
    ρ.range ≤ diagonalAction.range := by
  rintro _ ⟨a, rfl⟩
  exact exists_diagonal_of_axes (ρ a) (hs a) (hd a)

theorem range_eq_diagonal_of_moves_scalar {A : Type*} [Group A]
    (ρ : A →* MulAut Model.CubicPlane)
    (hs : ∀ a, Model.scalarAxis.map (ρ a).toMonoidHom = Model.scalarAxis)
    (hd : ∀ a, Model.derivedAxis.map (ρ a).toMonoidHom = Model.derivedAxis)
    (hf : diagonalAction derivedFlip ∈ ρ.range)
    (hm : ∃ a : A, ∃ c : Model.C3, ρ a (c, 1) ≠ (c, 1)) :
    ρ.range = diagonalAction.range := by
  apply le_antisymm (range_le_diagonal ρ hs hd)
  obtain ⟨a, c, hc⟩ := hm
  obtain ⟨s, he⟩ := exists_diagonal_of_axes (ρ a) (hs a) (hd a)
  have hs0 : s 0 ≠ 1 := by
    intro h
    apply hc
    rw [← he]
    change (signAut (s 0) c, signAut (s 1) 1) = (c, 1)
    simp [signAut, h]
  have hsmem : diagonalAction s ∈ ρ.range := ⟨a, he.symm⟩
  rintro _ ⟨t, rfl⟩
  have ht := (show ∀ s : E4, s 0 ≠ 1 → ∀ t : E4,
    t = 1 ∨ t = derivedFlip ∨ t = s ∨ t = s * derivedFlip by decide +kernel) s hs0 t
  rcases ht with rfl | rfl | rfl | rfl
  · simp
  · exact hf
  · exact hsmem
  · rw [map_mul]
    exact ρ.range.mul_mem hsmem hf

noncomputable def imageEquivE4 {A : Type*} [Group A]
    (ρ : A →* MulAut Model.CubicPlane)
    (hs : ∀ a, Model.scalarAxis.map (ρ a).toMonoidHom = Model.scalarAxis)
    (hd : ∀ a, Model.derivedAxis.map (ρ a).toMonoidHom = Model.derivedAxis)
    (hf : diagonalAction derivedFlip ∈ ρ.range)
    (hm : ∃ a : A, ∃ c : Model.C3, ρ a (c, 1) ≠ (c, 1)) :
    ρ.range ≃* E4 :=
  (MulEquiv.subgroupCongr (range_eq_diagonal_of_moves_scalar ρ hs hd hf hm)).trans
    diagonalRangeEquiv

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer.Diagonal

end
