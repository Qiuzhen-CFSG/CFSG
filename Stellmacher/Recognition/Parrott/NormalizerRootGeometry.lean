module

public import Stellmacher.Recognition.Parrott.NormalizerRootWordData
public import Stellmacher.Recognition.Parrott.NormalizerRootWordUniqueness
public import Stellmacher.Recognition.Parrott.NormalizerRootWordSquares

/-!
# Parrott's two-coset root geometry

For every order-four element m of K = O₂(N_G(F)) outside omega, its square
lies outside F, its centralizer in F has order eight, and every element of K
with the same square lies in mF or m⁻¹F.

The unique ordered words exhaust K by its cardinality. Their proved square
calculation therefore gives the general geometry. Both coordinate uniqueness
and the calculation use the supplied frame, so the assembly retains all its
elementary and fusion witnesses.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, the sixteen-root paragraph.
-/

open Subgroup
namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- The general two-coset geometry, obtained from the faithful ordered words
and their square calculation on the supplied Sylow frame. -/
public theorem ParrottSylowGeneratorData.normalizer_root_geometry
    (f : ParrottSylowGeneratorData n) (h : ParrottCentralizerHypotheses z) :
    let N := normalizer (e.F : Set G)
    let K := (pCore 2 N).map N.subtype
    let U := (omega₁ (pCore 2 N) (p := 2)).map (N.subtype.comp (pCore 2 N).subtype)
    ∀ m ∈ K, m ∉ U → orderOf m = 4 →
      m ^ 2 ∉ e.F ∧ Nat.card (e.F ⊓ centralizer ({m} : Set G) : Subgroup G) = 8 ∧
      ∀ g ∈ K, g ^ 2 = m ^ 2 → m⁻¹ * g ∈ e.F ∨ m * g ∈ e.F := by
  have hinj := f.normalizerRootWord_injective h
  exact f.normalizer_root_geometry_of_word_calculation hinj
    (ParrottNormalizerRootSquare.word_calculation f hinj)

/-- Parrott's square exclusion, centralizer count, and two-coset exhaustion
for the exact supplied centralizer frame. -/
public theorem ParrottCentralizerGeneratorData.normalizer_root_geometry
    (f : ParrottCentralizerGeneratorData n) (h : ParrottCentralizerHypotheses z) :
    let N := normalizer (e.F : Set G)
    let K := (pCore 2 N).map N.subtype
    let U := (omega₁ (pCore 2 N) (p := 2)).map (N.subtype.comp (pCore 2 N).subtype)
    ∀ m ∈ K, m ∉ U → orderOf m = 4 →
      m ^ 2 ∉ e.F ∧ Nat.card (e.F ⊓ centralizer ({m} : Set G) : Subgroup G) = 8 ∧
      ∀ g ∈ K, g ^ 2 = m ^ 2 → m⁻¹ * g ∈ e.F ∨ m * g ∈ e.F :=
  f.toParrottSylowGeneratorData.normalizer_root_geometry h

end Stellmacher.Recognition
