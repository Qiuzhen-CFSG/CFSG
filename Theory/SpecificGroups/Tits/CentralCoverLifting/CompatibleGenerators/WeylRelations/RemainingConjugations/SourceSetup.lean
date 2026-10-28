module
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.SourceWords
import Mathlib.Tactic.Group
/-!
# Interpreting the word calculations in the normalized presentation

The original power/root relations and the ten correction equations supply
all 37 input identities, retaining central errors exactly where they remain.
In particular VIII(s₁) is already exact, VIII(s₃) has the VII(s₃) error,
and VIII(r₃) has the product of that error and the square of VII(r₃)'s error.
The signed letters evaluate to the literal normalized generators.

Source: Parrott (1972), §5, p.683; the two odd-order eliminations are from
`WeylRelations.OddOrder`.
-/
public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false

@[expose] def relatorValue (j : ParrottRelatorIndex) : Subgroup.center NormalizedPresentation :=
  ⟨FreeGroup.lift normalizedGenerator (parrottRelator j), normalizedGenerator_relators_central j⟩

@[expose] def letterValue : Letter → NormalizedPresentation
  | .a => normalizedGenerator .r1
  | .b => normalizedGenerator .r8
  | .c => normalizedGenerator .s1
  | .d => normalizedGenerator .s2
  | .e => normalizedGenerator .s3
  | .f => normalizedGenerator .s4
  | .g => normalizedGenerator .s5
  | .h => normalizedGenerator .s6
  | .i => normalizedGenerator .s7
  | .j => normalizedGenerator .s8
  | .E => (normalizedGenerator .s3)⁻¹
  | .G => (normalizedGenerator .s5)⁻¹
  | .I => (normalizedGenerator .s7)⁻¹

variable (hroot : ∀ j, isPowerRootRelator j = true →
  FreeGroup.lift normalizedGenerator (parrottRelator j) = 1)
include hroot

private theorem inv_of_root_square (j : ParrottGenerator) (k : ParrottRelatorIndex)
    (hk : isPowerRootRelator k = true)
    (hw : parrottRelator k = (FreeGroup.of j) ^ 2) :
    (normalizedGenerator j)⁻¹ = normalizedGenerator j := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [hw, pow_two, map_mul, FreeGroup.lift_apply_of] using hroot k hk

@[expose] def normalizedContext : Context NormalizedPresentation where
  gen := letterValue
  inverse := by
    intro x
    cases x <;> simp only [flip, letterValue, inv_inv]
    all_goals symm
    · exact inv_of_root_square hroot .r1 .i_r1 rfl rfl
    · exact inv_of_root_square hroot .r8 .i_r8 rfl rfl
    · exact inv_of_root_square hroot .s1 .i_s1 rfl rfl
    · exact inv_of_root_square hroot .s2 .i_s2 rfl rfl
    · exact inv_of_root_square hroot .s4 .i_s4 rfl rfl
    · exact inv_of_root_square hroot .s6 .i_s6 rfl rfl
    · exact inv_of_root_square hroot .s8 .i_s8 rfl rfl
  central := ![relatorValue .vi_r1_r8, relatorValue .vii_s4, 1,
    relatorValue .vii_s3, relatorValue .vii_r3, relatorValue .viii_s2, 1]

/-- The original relators retain exactly the displayed central errors. -/
theorem normalized_relator_value : ∀ j,
    FreeGroup.lift normalizedGenerator (parrottRelator j) =
      ((normalizedContext hroot).scalar (sourceCoeff j) : NormalizedPresentation) := by
  have h5 := weyl_vii_s5_relation hroot
  have h4 := weyl_viii_s4_relation hroot
  have hvii2 : FreeGroup.lift normalizedGenerator (parrottRelator .vii_s2) = 1 := by
    simpa [correctionWord, hroot .i_r1 rfl, hroot .iii_s1_s7 rfl,
      hroot .v_s7_s4 rfl] using normalizedGenerator_correctionWord .s8
  have hviii7 : FreeGroup.lift normalizedGenerator (parrottRelator .viii_s7) = 1 := by
    simpa [correctionWord, hroot .iii_s1_s8 rfl, hroot .v_s5_s4 rfl, h4] using
      normalizedGenerator_correctionWord .s1
  have hvi1 : FreeGroup.lift normalizedGenerator (parrottRelator .vi_s1_r1) = 1 := by
    simpa [correctionWord, hroot .i_r1 rfl, hroot .i_r8 rfl, hroot .iii_s1_s8 rfl,
      hroot .v_s5_s4 rfl, h5, hviii7] using normalizedGenerator_correctionWord .r1
  have hvi8 : FreeGroup.lift normalizedGenerator (parrottRelator .vi_r8_s8) = 1 := by
    simpa [correctionWord, hroot .i_r1 rfl, hroot .iii_s1_s7 rfl,
      hroot .v_s7_s4 rfl, hvii2, h4] using normalizedGenerator_correctionWord .r8
  have hviii3 : FreeGroup.lift normalizedGenerator (parrottRelator .viii_s3) =
      FreeGroup.lift normalizedGenerator (parrottRelator .vii_s3) := by
    symm
    apply inv_mul_eq_one.mp
    simpa [correctionWord, hroot .i_s1 rfl, hroot .v_s5_s4 rfl, h4] using
      normalizedGenerator_correctionWord .s3
  have hviii1 : FreeGroup.lift normalizedGenerator (parrottRelator .viii_s1) = 1 := by
    have hh : FreeGroup.lift normalizedGenerator (parrottRelator .vii_s3) *
        (FreeGroup.lift normalizedGenerator (parrottRelator .viii_s1))⁻¹ *
        (FreeGroup.lift normalizedGenerator (parrottRelator .vii_s3))⁻¹ = 1 := by
      simpa [correctionWord, hroot .iii_s1_s8 rfl, hroot .v_s5_s4 rfl,
        h5, h4, hviii3] using normalizedGenerator_correctionWord .s5
    exact inv_eq_one.mp (mul_eq_left.mp (mul_inv_eq_one.mp hh))
  have hviiir3 : FreeGroup.lift normalizedGenerator (parrottRelator .viii_r3) =
      FreeGroup.lift normalizedGenerator (parrottRelator .vii_s3) *
      (FreeGroup.lift normalizedGenerator (parrottRelator .vii_r3)) ^ 2 := by
    have hh : (FreeGroup.lift normalizedGenerator (parrottRelator .vii_r3)) ^ (-2 : ℤ) *
        (FreeGroup.lift normalizedGenerator (parrottRelator .vii_s3))⁻¹ *
        FreeGroup.lift normalizedGenerator (parrottRelator .viii_r3) = 1 := by
      simpa [correctionWord, hroot .i_r1 rfl, hviii1, hviii7, hviii3] using
        normalizedGenerator_correctionWord .s7
    calc
      _ = ((FreeGroup.lift normalizedGenerator (parrottRelator .vii_r3)) ^ (-2 : ℤ) *
          (FreeGroup.lift normalizedGenerator (parrottRelator .vii_s3))⁻¹)⁻¹ *
          ((FreeGroup.lift normalizedGenerator (parrottRelator .vii_r3)) ^ (-2 : ℤ) *
          (FreeGroup.lift normalizedGenerator (parrottRelator .vii_s3))⁻¹ *
          FreeGroup.lift normalizedGenerator (parrottRelator .viii_r3)) := by group
      _ = _ := by rw [hh]; group
  intro j
  cases j <;> simp [sourceCoeff, Context.scalar, normalizedContext, relatorValue]
  all_goals first | exact hroot _ rfl | assumption

private theorem sourceWord_value (j : ParrottRelatorIndex) :
    (normalizedContext hroot).value (sourceWord j) =
      FreeGroup.lift normalizedGenerator (parrottRelator j) := by
  have h1 := inv_of_root_square hroot .r1 .i_r1 rfl rfl
  have h2 := inv_of_root_square hroot .s2 .i_s2 rfl rfl
  have hc := inv_of_root_square hroot .s1 .i_s1 rfl rfl
  have h4 := inv_of_root_square hroot .s4 .i_s4 rfl rfl
  have h6 := inv_of_root_square hroot .s6 .i_s6 rfl rfl
  have hj := inv_of_root_square hroot .s8 .i_s8 rfl rfl
  cases j <;> simp only [Context.value, normalizedContext, sourceWord, letterValue,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, parrottRelator,
    parrottCommutator, parrottR3, parrottR5, parrottR7, map_mul, map_inv,
    FreeGroup.lift_apply_of, pow_succ, pow_zero, mul_inv_rev, inv_inv,
    h1, h2, hc, h4, h6, hj, mul_one, one_mul, mul_assoc]

/-- The literal auxiliary presentation satisfies every replay input under `hroot`.
No remaining conjugation identity or braid equation is assumed. -/
theorem normalized_source : Source (normalizedContext hroot) := by
  intro j
  constructor
  rw [sourceWord_value hroot, normalized_relator_value hroot]
  simp only [Context.value, List.map_nil, List.prod_nil, one_mul]

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
