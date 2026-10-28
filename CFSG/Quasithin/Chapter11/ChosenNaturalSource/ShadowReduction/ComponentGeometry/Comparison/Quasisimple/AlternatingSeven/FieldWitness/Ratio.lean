module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness.Rows
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.Rank

/-!
# Ratio one and the original two-rank equality in 11.4.2

The natural moved quotient has ratio one. Codimension monotonicity rules
out strong offenders on the offender restriction; replacement rules them
out on the original centralizer quotient. Its FF witness then gives equality.
The existing B.2.4 application yields m2(R1) = m2(T), with no ratio premise.

Source: Aschbacher--Smith, 11.4.2, printed p.777, and B.2.4(3).
The earlier PSL2 quotient marking is produced by the natural flag Cartan
argument and remains an explicit input for the upstream assembly.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- Ratio one holds on the original action, not only on its moved quotient. -/
theorem quadraticRatio_eq_one
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hmodel : AlternatingSevenModel E) (hff : IsFFModule (action E))
    (e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) E.input.field.Carrier) :
    quadraticRatio (action E) = 1 := by
  obtain ⟨_,s,_,_,_,hq⟩ := exists_six_section E h hf hne hstar hcent hmodel hff e
  have hbound := ratio_ge_one_of_section s hq
  have hn : ¬ IsStrongFFModule (offenderAction E) := fun hs =>
    (not_lt_of_ge hbound) ((isStrongFFModule_iff_quadraticRatio_lt_one _).mp hs)
  have hn' := not_strong_of_offenderSubgroup (action E) hn
  exact le_antisymm ((isFFModule_iff_quadraticRatio_le_one _).mp hff)
    (le_of_not_gt (fun hlt => hn' ((isStrongFFModule_iff_quadraticRatio_lt_one _).mpr hlt)))

/-- The source rank equality with the ratio premise discharged by B.5.1. -/
theorem twoRank_radical_eq_sylow
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hmodel : AlternatingSevenModel E) (hff : IsFFModule (action E))
    (e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) E.input.field.Carrier) :
    ChapterB.twoRank E.R₁ = ChapterB.twoRank (T : Subgroup G) :=
  twoRank_radical_eq_sylow_of_ratio E h hf hne hstar hcent
    (quadraticRatio_eq_one E h hf hne hstar hcent hmodel hff e).ge


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness
