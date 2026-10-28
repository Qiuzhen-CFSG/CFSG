module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.SymplecticTwo
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.SplitModels

/-!
# Exhaustive comparison of the B.4.2 action catalogue

Every source constructor is retained. The binary symplectic derived endpoint
is identified with its actual alternating-six natural action, while degree-one
fields are changed by a field equivalence. Nonbinary rank-two and rank-one
rows retain their actual action markings for their source elimination owners.
Source: Aschbacher--Smith B.4.2 and 12.2.2, pp.86,795.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ModuleClassification
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.ExtensionConsequences
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]

inductive SourceRow (ρ : Representation (ZMod 2) A W) (K : Subgroup A) : Prop
  | rankOne (F : BinaryField) (e : ActionEquiv (ρ.comp K.subtype) (linearNatural F 2))
  | linearThree (e : ActionEquiv (ρ.comp K.subtype) (linearNatural BinaryField.two 3))
  | nonbinaryLinearThree (F : BinaryField) (hF : 1 < F.degree)
      (e : ActionEquiv (ρ.comp K.subtype) (linearNatural F 3))
  | symplectic (F : BinaryField) (hF : 1 < F.degree)
      (e : ActionEquiv (ρ.comp K.subtype) (binarySymplectic F))
  | g2 (F : BinaryField) (hF : 1 < F.degree)
      (e : ActionEquiv (ρ.comp K.subtype) (binaryG2 F))
  | derivedG2 (e : ActionEquiv (ρ.comp K.subtype) (g2DerivedNatural (ZMod 2)))
  | alternating (n : ℕ) (hn : 5 ≤ n) (hn' : n ≤ 8)
      (e : ActionEquiv (ρ.comp K.subtype) (alternatingNatural n))
  | alternatingSevenFour (e : K ≃* alternatingGroup (Fin 7))
      (hd : Module.finrank (ZMod 2) W = 4)
  | tripleSix (a : TripleSixAction ρ K)
  | binaryLinear (d : ℕ) (hd : d = 4 ∨ d = 5)
      (e : ActionEquiv (ρ.comp K.subtype) (linearNatural BinaryField.two d))
  | exteriorFive (e : K ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
      (hd : Module.finrank (ZMod 2) W = 10)

theorem sourceRow_of_irreducible {ρ : Representation (ZMod 2) A W} {K J : Subgroup A}
    (h : IrreducibleActionCase ρ K J) : SourceRow ρ K := by
  cases h with
  | linearTwo F _ e _ _ => exact .rankOne F e
  | linearThree F _ e _ =>
    by_cases hF : F.degree = 1
    · exact .linearThree (e.trans (degreeOneNaturalEquiv F hF 3))
    · exact .nonbinaryLinearThree F (by have := F.degree_pos; omega) e
  | symplectic F hF _ e _ => exact .symplectic F hF e
  | symplecticTwo e _ =>
    exact .alternating 6 (by decide) (by decide)
      ((markedRestriction e).trans SymplecticTwo.derivedNaturalActionEquiv)
  | g2 F hF _ e _ _ => exact .g2 F hF e
  | g2Two e _ _ => exact .derivedG2 (markedRestriction e)
  | symmetric n hn e _ _ => exact .alternating n (by omega) (by omega) (markedRestriction e)
  | alternatingSix _ e _ _ => exact .alternating 6 (by decide) (by decide) e
  | alternatingSeven _ _ e hd _ _ => exact .alternatingSevenFour e hd
  | tripleSix _ a _ => exact .tripleSix a
  | binaryLinear d hd _ e _ => exact .binaryLinear d hd e
  | orthogonalSix _ _ e _ _ => exact .alternating 8 (by decide) (by decide) e
  | symmetricEight _ e _ => exact .alternating 8 (by decide) (by decide) (markedRestriction e)
  | exteriorFive _ _ e hd _ _ => exact .exteriorFive e hd

end CFSG.Quasithin.Chapter12.Section02.ModuleClassification
