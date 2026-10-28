module

public import CFSG.Quasithin.ChapterJ.Defs
public import CFSG.Quasithin.ChapterJ.Section01To02.Preliminaries
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Center
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Transvections

/-!
# The literal conjugates in J.2.2(5)

Every L-conjugate of U contains V and lies in S, hence in H. Its order
is 32. Conjugating the relative H-normality of U shows that it is
normalized by the centralizer of the corresponding conjugate of Z.
These statements use the actual ambient conjugation maps.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(5), printed pp.432–433 (PDF pp.443–444).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.ConjugateIntersections
open Subgroup Representation
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]

/-- The source's Uα, with left conjugation as used by the section coordinates. -/
abbrev conjugateU (d : LocalSetup G) (l : G) : Subgroup G :=
  d.toTypeRuSetup.U.map (MulAut.conj l).toMonoidHom

/-- The center marking transported by the same conjugation as Uα. -/
abbrev conjugateZ (d : LocalSetup G) (l : G) : Subgroup G :=
  d.toTypeRuSetup.Z.map (MulAut.conj l).toMonoidHom

/-- All the conjugates contain the same normal subgroup V. -/
theorem V_le_conjugateU (d : LocalSetup G) (l : G) (hl : l ∈ d.L) :
    d.V ≤ conjugateU d l := by
  have hn : l ∈ normalizer d.V := d.ru1.normalizer_eq ▸ hl
  calc
    d.V = d.V.map (MulAut.conj l).toMonoidHom :=
      (mem_normalizer_iff_map_conj_eq.mp hn).symm
    _ ≤ conjugateU d l := map_mono (le_conjugateSpan _ _)

/-- The normal two-core S contains every conjugate under L. -/
theorem conjugateU_le_S (d : LocalSetup G) (l : G) (hl : l ∈ d.L) :
    conjugateU d l ≤ d.toTypeRuSetup.S := by
  calc
    conjugateU d l ≤ d.toTypeRuSetup.S.map (MulAut.conj l).toMonoidHom :=
      map_mono d.U_le_S
    _ = d.toTypeRuSetup.S :=
      mem_normalizer_iff_map_conj_eq.mp (d.ru1.steinberg.normalized hl)

/-- In particular, the star image in H/Q is defined for every L-conjugate. -/
theorem conjugateU_le_H (d : LocalSetup G) (l : G) (hl : l ∈ d.L) :
    conjugateU d l ≤ d.toTypeRuSetup.H :=
  (conjugateU_le_S d l hl).trans d.S_le_H

/-- Conjugation preserves the order 32 calculated in J.2.2(2). -/
theorem card_conjugateU (d : LocalSetup G) (l : G) :
    Nat.card (conjugateU d l) = 32 := by
  rw [conjugateU, card_map_of_injective (MulAut.conj l).injective]
  exact d.ru2.card_U d.card_Z

/-- The common subgroup is already in the centralizer kernel HC. -/
theorem V_le_HC (d : LocalSetup G) : d.V ≤ d.toTypeRuSetup.HC :=
  (le_conjugateSpan _ _).trans d.U_le_HC

/-- The transported center lies in V, hence in the original U. -/
theorem conjugateZ_le_V (d : LocalSetup G) (l : G) (hl : l ∈ d.L) :
    conjugateZ d l ≤ d.V := by
  have hn : l ∈ normalizer d.V := d.ru1.normalizer_eq ▸ hl
  calc
    conjugateZ d l ≤ d.V.map (MulAut.conj l).toMonoidHom :=
      map_mono (d.center_eq.le.trans inf_le_left)
    _ = d.V := mem_normalizer_iff_map_conj_eq.mp hn

/-- Relative normality transports to the literal centralizer of Zα. -/
theorem conjugateU_normalized (d : LocalSetup G) (l : G) :
    centralizer (conjugateZ d l : Set G) ≤ normalizer (conjugateU d l) := by
  apply le_normalizer_iff.mpr
  intro x hx a ha
  obtain ⟨u, hu, rfl⟩ := ha
  have hH : l⁻¹ * x * l ∈ d.toTypeRuSetup.H := by
    intro z hz
    have h := hx (l * z * l⁻¹) (mem_map.mpr ⟨z, hz, rfl⟩)
    have he := congrArg (fun y : G => l⁻¹ * y * l) h
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      inv_mul_cancel, mul_inv_cancel, one_mul, mul_one] using he
  have hu' := (mem_normalizer_iff.mp (d.ru2.natural.normalized hH) u).mp hu
  refine mem_map.mpr ⟨_, hu', ?_⟩
  change l * (l⁻¹ * x * l * u * (l⁻¹ * x * l)⁻¹) * l⁻¹ =
    x * (l * u * l⁻¹) * x⁻¹
  group

/-- The H-stabilizer fixes U with the same conjugation convention. -/
theorem conjugateU_eq_of_mem_H (d : LocalSetup G) (l : G)
    (hl : l ∈ d.toTypeRuSetup.H) : conjugateU d l = d.toTypeRuSetup.U :=
  mem_normalizer_iff_map_conj_eq.mp (d.ru2.natural.normalized hl)

/-- Thus a distinct conjugate is indexed by an element outside H. -/
theorem not_mem_H_of_conjugateU_ne (d : LocalSetup G) (l : G)
    (hne : conjugateU d l ≠ d.toTypeRuSetup.U) : l ∉ d.toTypeRuSetup.H :=
  fun hl => hne (conjugateU_eq_of_mem_H d l hl)

end CFSG.Quasithin.ChapterJ.ConjugateIntersections
