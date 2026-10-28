module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.MiddleCore.Core

/-!
# Entrywise descriptions of the middle residual-flag radicals

The large 3×3 block is identity, the small 2×2 block is upper unitriangular,
and the lower-left rectangle is zero. There is no restriction on the
upper-right rectangle. These are the embedded O₂(H₂) and O₂(H₃), not
O₂ of the full parabolics.

Source: Aschbacher–Smith, Lemma 12.5.2(1–2), printed p.817/PDF p.834.
-/

@[expose] public section
open scoped MatrixGroups
namespace Representation.SL5ExteriorSquare.MiddleCore
open SL5TenDimensional
open Theory.SpecificGroups.LinearSylowNormalizers

theorem mem_smallUnipotent (a : SL(2, ZMod 2)) :
    a ∈ smallUnipotent ↔ a.val 0 0 = 1 ∧ a.val 1 0 = 0 ∧ a.val 1 1 = 1 := by
  rw [mem_unipotent, mem_borel]
  constructor
  · rintro ⟨hu, hd⟩
    exact ⟨hd 0, hu (by decide), hd 1⟩
  · rintro ⟨h0, h10, h1⟩
    constructor
    · intro i j hji
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i
      fin_cases i
      · exact h0
      · exact h1

theorem mem_twoRadical (g : parabolic 2) : g.val ∈ twoRadical ↔
    parabolicTwoSmallBlock g ∈ smallUnipotent ∧ twoLargeHom g = 1 :=
  Subgroup.mem_map_iff_mem (parabolic 2).subtype_injective

theorem mem_threeRadical (g : parabolic 3) : g.val ∈ threeRadical ↔
    threeLargeHom g = 1 ∧ parabolicThreeSmallBlock g ∈ smallUnipotent :=
  Subgroup.mem_map_iff_mem (parabolic 3).subtype_injective

/-- All restrictions on the ambient 5×5 matrix; the upper-right block is free. -/
theorem mem_twoRadical_entries (g : Group) : g ∈ twoRadical ↔
    (∀ i j : Fin 5, 2 ≤ i.val → j.val < 2 → g.val i j = 0) ∧
    (g.val 0 0 = 1 ∧ g.val 1 0 = 0 ∧ g.val 1 1 = 1) ∧
    (∀ i j : Fin 3, g.val ⟨2+i.val, by omega⟩ ⟨2+j.val, by omega⟩ =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(mem_parabolic_iff_lowerLeft_zero 2 x.val).mp x.property, ?_, ?_⟩
    · have hs := (mem_smallUnipotent (parabolicTwoSmallBlock x)).mp hx.1
      simp only [parabolicTwoSmallBlock_entry] at hs
      exact hs
    · intro i j
      exact (parabolicLeviHom_snd_entry 2 (by decide) x i j).symm.trans
        (congrArg (fun a : SL(3, ZMod 2) => a.val i j) (show twoLargeHom x = 1 from hx.2))
  · rintro ⟨hp, hs, hl⟩
    let x : parabolic 2 := ⟨g, (mem_parabolic_iff_lowerLeft_zero 2 g).mpr hp⟩
    apply (mem_twoRadical x).mpr
    constructor
    · apply (mem_smallUnipotent _).mpr
      exact ⟨(parabolicTwoSmallBlock_entry x 0 0).trans hs.1,
        (parabolicTwoSmallBlock_entry x 1 0).trans hs.2.1,
        (parabolicTwoSmallBlock_entry x 1 1).trans hs.2.2⟩
    · apply Subtype.ext
      ext i j
      exact (parabolicLeviHom_snd_entry 2 (by decide) x i j).trans (hl i j)

/-- The analogous entrywise description with the blocks in the opposite order. -/
theorem mem_threeRadical_entries (g : Group) : g ∈ threeRadical ↔
    (∀ i j : Fin 5, 3 ≤ i.val → j.val < 3 → g.val i j = 0) ∧
    (∀ i j : Fin 3, g.val (Fin.castLE (by decide) i) (Fin.castLE (by decide) j) =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) ∧
    (g.val 3 3 = 1 ∧ g.val 4 3 = 0 ∧ g.val 4 4 = 1) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(mem_parabolic_iff_lowerLeft_zero 3 x.val).mp x.property, ?_, ?_⟩
    · intro i j
      exact (parabolicLeviHom_fst_entry 3 (by decide) x i j).symm.trans
        (congrArg (fun a : SL(3, ZMod 2) => a.val i j) (show threeLargeHom x = 1 from hx.1))
    · have hs := (mem_smallUnipotent (parabolicThreeSmallBlock x)).mp hx.2
      simp only [parabolicThreeSmallBlock_entry] at hs
      exact hs
  · rintro ⟨hp, hl, hs⟩
    let x : parabolic 3 := ⟨g, (mem_parabolic_iff_lowerLeft_zero 3 g).mpr hp⟩
    apply (mem_threeRadical x).mpr
    constructor
    · apply Subtype.ext
      ext i j
      exact (parabolicLeviHom_fst_entry 3 (by decide) x i j).trans (hl i j)
    · apply (mem_smallUnipotent _).mpr
      exact ⟨(parabolicThreeSmallBlock_entry x 0 0).trans hs.1,
        (parabolicThreeSmallBlock_entry x 1 0).trans hs.2.1,
        (parabolicThreeSmallBlock_entry x 1 1).trans hs.2.2⟩

end Representation.SL5ExteriorSquare.MiddleCore
