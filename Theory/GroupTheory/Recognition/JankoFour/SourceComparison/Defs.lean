module

public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Defs

/-!
# The original cubic normalizer input to the J₄ comparison

The centralizer here lies in H = C_G(z), before quotienting by its marked
central involution. Section 8 uses its perfectness and an involutory splitting
of its normalizer. These are precisely the additional clauses of AS91 (4.9)
retained by the section 4 constructor. The quotient centralizer from (4.1)
does not imply this perfectness.

The record refers to the same cubic Sylow and quotient as `LocalData`. It
contains no comparison map, automorphism classification or recognition claim.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (4.9), (8.3), pp.599,606–607,
DOI 10.1007/BF01232280.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The original cubic centralizer, with its central involution retained. -/
abbrev cubicCentralizerInH
    (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
    (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)) : Subgroup (centralizer z) :=
  Subgroup.centralizer (cubicSylowImage e X : Set (centralizer z))

/-- The original cubic normalizer in H. -/
abbrev cubicNormalizerInH
    (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
    (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)) : Subgroup (centralizer z) :=
  Subgroup.normalizer (cubicSylowImage e X : Set (centralizer z))

/-- Literal section 4 input, indexed by the unchanged earlier local data. -/
structure CubicNormalizerData {h : IsTypeJ4 z} (a : SourceIncidence.LocalData h) where
  perfect : Group.IsPerfect (cubicCentralizerInH a.e a.X)
  s : centralizer z
  s_mem : s ∈ cubicNormalizerInH a.e a.X
  s_sq : s * s = 1
  s_not_mem : s ∉ cubicCentralizerInH a.e a.X

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
