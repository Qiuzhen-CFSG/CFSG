module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.SameAxis.Geometry
public import Theory.Representation.BinaryOffender.NormalizerQuadratic

/-!
# Propagation of quadraticity through the two source normalizers

First, the conjugates of a quadratic subgroup B under the normalizer of C
all fix [V,C]. If they generate R, then R fixes [V,C]. Conjugating by the
normalizer of R shows that every conjugate of C has displacement in C_V(R).
If these conjugates generate R, then [V,R] is fixed by R.

The proof uses the actual representation operators and subgroup joins. It
requires neither a split extension nor quadraticity of the individual
ambient elements as an extra premise. The two geometric generation claims
remain explicit until the rank-four geometry supplies them.
Source: Aschbacher–Smith, B.4.9, final paragraph on printed p.95,
combined manuscript of 1 March 2004.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive.SameAxis
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The upstairs action step in the rank-four source argument. Both
normalizers and their conjugate-generated subgroups are in the original G. -/
theorem quadratic_of_normalizer_generation {B C R : Subgroup G}
    (hB : IsQuadratic ρ B) (hCB : C ≤ B) (hgen : NormalizerGeneration B C R) :
    IsQuadratic ρ R :=
  quadratic_of_conjugate_generation ρ hB hCB inf_le_right le_rfl hgen.1 hgen.2

open QuasisimpleSource
variable {F : BinaryField}

/-- The propagated radical action supplies the literal source four-group
hypothesis, even when no suitable four-group lies in the initial offender. -/
theorem axisFour_of_normalizer_generation (d : DoubleNatural F 5 ρ)
    {B C R E : Subgroup G} (hB : IsQuadratic ρ B) (hCB : C ≤ B)
    (hgen : NormalizerGeneration B C R) (hER : E ≤ R)
    (hE : QuadraticSplitting.IsAxisFour d E) : HasQuadraticAxisFour d := by
  have hR := quadratic_of_normalizer_generation ρ hB hCB hgen
  exact ⟨E, hE, fun a ha b hb v => hR a (hER ha) b (hER hb) v⟩

end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive.SameAxis
