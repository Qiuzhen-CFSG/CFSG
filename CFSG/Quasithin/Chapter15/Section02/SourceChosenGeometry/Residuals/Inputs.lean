module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Definitions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements

/-!
# The original input and output of the residual recognition in 15.2.12

The input retains the chosen full-or-proper module, the preceding wreath
recognition, and the actual offender plane of 15.2.11. It contains no
residual-recognition, prime-complement-residual, or full-support conclusion.
The structural alternatives below are a target, not an asserted theorem.
They retain the component embeddings, conjugator, subgroup product, and
actual quotient isomorphisms.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.9--12, printed pp.1110--1111.
-/

@[expose] public section

open Subgroup Stellmacher Theory.GroupTheory
open scoped Pointwise

namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open ChapterA.Section05To06

variable {G : Type*} [Group G] [Finite G]

/-- Exactly the preceding inputs retained by the conditional 15.2.12 task. -/
structure ResidualInput {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (H B : Subgroup G) : Prop where
  outside : H ∈ Chapter3.HStar (T : Subgroup G) M
  quotient : Nonempty ((H ⧸ pCore 2 H) ≃*
    RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))
  two_overgroups : maximalTwoLocalOvergroups (T : Subgroup G) = {M, Mc}
  offender : B ∈ sigmaOutside (T : Subgroup G) H
  plane_card : Nat.card (⁅V, B⁆ : Subgroup G) = 4
  plane_normalized : H ≤ normalizer ((⁅V, B⁆ : Subgroup G) : Set G)
  plane_central : ⁅V, B⁆ ≤ (center (residual H)).map (residual H).subtype

/-- The three structural alternatives of original 15.2.12(2).
The classical model in the invariant row also records the component
quotient supplied by 1.3.4, for use in the residual calculation. -/
def StructuralAlternatives (T : Sylow 2 G) (H Mc : Subgroup G) : Prop :=
  partnerSpan H Mc = residual H ∨
    (partnerSpan H Mc ∈ Chapter1.LStar G (T : Subgroup G) ∧
      partnerSpan H Mc ∈ Chapter1.cComponentsIn Mc ∧
      ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
        ClassicalGroup.IsPSL (Chapter1.XiQuotient (partnerSpan H Mc)) n 2 ∧
        Nonempty (((partnerSpan H Mc ⊔ (T : Subgroup G) : Subgroup G) ⧸
          pCore 2 (partnerSpan H Mc ⊔ (T : Subgroup G) : Subgroup G)) ≃*
          MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))) ∨
    ∃ (L : Subgroup G) (t : G),
      L ∈ Chapter1.LStar G (T : Subgroup G) ∧ L ∈ Chapter1.cComponentsIn Mc ∧
      t ∈ (T : Subgroup G) ∧ t ∉ normalizer (L : Set G) ∧
      partnerSpan H Mc = L ⊔ L.conjBy t ∧
      (partnerSpan H Mc : Set G) = (L : Set G) * (L.conjBy t : Set G) ∧
      ((∃ n : ℕ, Even n ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient L) 2 (2 ^ n)) ∨
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient L) 2 p)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
