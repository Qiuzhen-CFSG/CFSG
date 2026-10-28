module
public import CFSG.Quasithin.ChapterB.Section04.SmallRecognition.BinaryFourMarked.Classification
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.HeadHypotheses

/-!
# Discharging the fixed-marking B.4 input in 13.8.25

The proved binary L₄ classification supplies the exact natural, dual and
exterior-square alternatives for each maximal quotient of the literal module.
The actor marking is unchanged and the actor and module universes are independent.
The strict-case source assembly remains with `qt-d-138-linear-strict-module-source`;
the final 13.8.25 assembly belongs to `qt-d-138-linear-source`.

Source: Aschbacher--Smith B.4.2(9--10), B.4.5 and 13.8.25,
printed pp.86--87,960--961 (combined manuscript, 1 March 2004).
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.OriginalSource
open ChiefFactors ChiefFactors.Alignment
universe u v
variable {H : Type u} [Group H]

/-- The precise `LinearB4` premise, now proved under the supplied actor marking. -/
theorem linearB4_source (eH : H ≃* BinaryLinear.GL NaturalSpace) : LinearB4.{v} eH := by
  intro E _ _ _ σ hf hi hq
  exact ChapterB.SmallRecognition.BinaryFourMarked.marked_alternatives σ eH hf hi hq

/-- Apply the classification to the actual maximal quotient and descended
quadratic actor in the strict-case chief-factor argument. -/
theorem maximal_quotient_alternatives_source [Finite H]
    {E : Type v} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (s : GeneratingSeed ρ)
    (eH : H ≃* BinaryLinear.GL NaturalSpace)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hb : fixedCodim ρ A ≤ 2 * rank A) (W : Subrepresentation ρ) (hW : IsCoatom W) :
    HeadAlternatives W.quotientRepresentation eH :=
  maximal_quotient_alternatives ρ s eH (linearB4_source eH) A hA hq hb W hW
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.OriginalSource
