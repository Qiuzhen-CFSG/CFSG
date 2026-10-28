module

public import Theory.SpecificGroups.G2Even.TwoRank.SourceBound
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.Complete
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.AdjointObstruction

/-!
# The source cubic degree bound for nonbinary G₂

The genuine full automorphism rank bound supplies both the tensor window and
the adjoint obstruction. Thus a faithful irreducible module with cubic ratio
at most two in its actual linear normalizer has degree below fourteen times
the field degree. No numerical or model-displacement premise remains.

Source: Guralnick–Malle, Classification of 2F-modules II, Lemma 8.5;
Aschbacher–Smith K.3, printed p.457.
-/

public section

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree
open Representation Representation.BinaryOffender

variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The complete numerical input to natural-module recognition, with all
automorphism, tensor and adjoint estimates discharged. -/
theorem source_degree_lt
    (σ : Representation (ZMod 2) (Atlas.G2.Model F) V) [IsIrreducible σ]
    {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (hf : Function.Injective σ)
    (hc : cubicRatio (normalizerRepresentation σ) ≤ 2) :
    Module.finrank (ZMod 2) V < 14 * r := by
  have hAut := Atlas.G2.EvenTwoRank.source_automorphism_two_rank_le F hr hF
  exact degree_lt_of_adjoint_estimate σ hr hF hf hc hAut
    (AdjointObstruction.quasiequivalent_cubic_obstruction σ hr hF hAut)

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree
