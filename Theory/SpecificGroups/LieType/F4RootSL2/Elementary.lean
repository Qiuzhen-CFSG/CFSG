module
public import Theory.SpecificGroups.LieType.F4RootSL2.Comparison
public import Theory.SpecificGroups.LieType.ExceptionalSplit.RootGeneration

/-!
# The long-root SL₂ inside the elementary F₄ matrix group

Restrict the explicit action on the full 52-dimensional lattice to the
literal elementary adjoint group. The upper and lower transvection formulas
agree with the canonical root curves at ±α₀; transvection generation proves
membership of every matrix in the image. Faithfulness is inherited from a
natural root-string block. The neighboring long simple root α₁ is named for
the subsequent central-quotient separation argument.

Source: GLS3 §2.6, the common-lattice subsystem construction
(`refs/KGroup/GLS3/chapter2.tex`), and the proper fundamental subgroup in
Aschbacher–Smith A.2.17, printed p.39 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
namespace ExceptionalSplit.F4RootSL2
open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _
local instance : InvolutiveNeg typeF4Roots := typeF4RootPairing.indexNeg

variable {F : Type*} [Field F]

abbrev fundamentalRoot := typeF4RootPairing_baseEquiv 0
abbrev neighborRoot := typeF4RootPairing_baseEquiv 1
abbrev Elementary (F : Type*) [Field F] :=
  rootGenerated typeF4RootPairing typeF4RootPairing_base F
abbrev upper (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t
abbrev lower (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t

lemma ambient_upper (t : F) : ambientHom (upper t) =
    (elementaryRoot typeF4RootPairing typeF4RootPairing_base F fundamentalRoot t).val := by
  rw [ambientHom_positive]
  exact (rootCurveUnit_simple fundamentalRoot t).symm

lemma ambient_lower (t : F) : ambientHom (lower t) =
    (elementaryRoot typeF4RootPairing typeF4RootPairing_base F
      (-fundamentalRoot : typeF4Roots) t).val := by
  rw [ambientHom_negative]
  exact (rootCurveUnit_neg_simple fundamentalRoot t).symm

lemma ambient_mem (A : SL(2, F)) : ambientHom A ∈
    rootGenerated typeF4RootPairing typeF4RootPairing_base F := by
  apply Matrix.SL2.transvection_induction (fun A => ambientHom A ∈
    rootGenerated typeF4RootPairing typeF4RootPairing_base F) ?_ ?_ A
  · intro i j hij t
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change ambientHom (upper t) ∈ _
      rw [ambient_upper]
      exact (elementaryRoot typeF4RootPairing typeF4RootPairing_base F fundamentalRoot t).property
    · change ambientHom (lower t) ∈ _
      rw [ambient_lower]
      exact (elementaryRoot typeF4RootPairing typeF4RootPairing_base F (-fundamentalRoot : typeF4Roots) t).property
    · exact (hij rfl).elim
  · intro A B hA hB
    rw [map_mul]
    exact Subgroup.mul_mem _ hA hB

/-- The faithful long-root homomorphism into the literal elementary F₄ matrix group. -/
def elementaryHom : SL(2, F) →* Elementary F :=
  ambientHom.codRestrict _ ambient_mem

lemma elementaryHom_injective : Function.Injective (elementaryHom (F := F)) := by
  intro A B h
  exact ambientHom_injective (congrArg Subtype.val h)

@[simp] lemma elementaryHom_upper (t : F) : elementaryHom (upper t) =
    elementaryRoot typeF4RootPairing typeF4RootPairing_base F fundamentalRoot t :=
  Subtype.ext (ambient_upper t)

@[simp] lemma elementaryHom_lower (t : F) : elementaryHom (lower t) =
    elementaryRoot typeF4RootPairing typeF4RootPairing_base F
      (-fundamentalRoot : typeF4Roots) t :=
  Subtype.ext (ambient_lower t)

end ExceptionalSplit.F4RootSL2

end
