module

public import CFSG.Quasithin.ChapterK.Defs
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Source inputs to K.3.2 module recognition

The ambient representation, its actual generalized Fitting subgroup and its
cubic ratio are retained. A covering map is a genuine surjective homomorphism
with central kernel, kept separate from the source hypotheses. In particular,
no module catalogue, dimension bound or scalar-extension comparison is an input
field. The earlier Theorem C and covering results supply the permitted linear
parameters and covering maps in the final Chapter K assembly.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Chapter K standing
hypotheses and K.3.2, printed pp.451 and 454; GM04 Proposition 4.6/Table 7.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition
open Theory.GroupTheory Representation.BinaryOffender ChapterB.QuasisimpleSource

universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

/-- The original source hypotheses, with no recognition conclusion. -/
structure SourceHypothesis (K : GroupClass.{u})
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) : Prop where
  finite_group : Finite G
  finite_module : FiniteDimensional (ZMod 2) V
  sqtk : IsSQTK K G
  fitting : generalizedFitting G = L
  quasisimple : IsQuasisimple L
  faithful : Function.Injective ρ
  irreducible : Representation.IsIrreducible (ρ.comp L.subtype)
  cubic_le_two : cubicRatio ρ ≤ 2

/-- The three permitted parameter families supplied by the earlier Theorem C. -/
def AdmissibleParameters (B : BinaryField) (d : ℕ) : Prop :=
  d = 3 ∨ ((d = 4 ∨ d = 5) ∧ B.degree = 1)

/-- A supplied earlier covering identification retains its literal quotient map. -/
structure LinearCover (B : BinaryField) (d : ℕ) (L : Subgroup G) where
  projection : Matrix.SpecialLinearGroup (Fin d) B.Carrier →* L
  surjective : Function.Surjective projection
  central_kernel : projection.ker ≤ Subgroup.center _

end CFSG.Quasithin.ChapterK.Linear.Recognition
