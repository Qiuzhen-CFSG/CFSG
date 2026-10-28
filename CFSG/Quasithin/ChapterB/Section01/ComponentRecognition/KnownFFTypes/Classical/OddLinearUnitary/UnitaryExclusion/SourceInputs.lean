module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.Restrictions
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.Representation.BinaryOffender.CubicRatio

/-!
# Source inputs for the odd-prime PSU₃ branch of K.2

The source actor is a finite SQTK group for the full known-simple catalogue,
with quasisimple F* acting faithfully and irreducibly on the binary module.
The unitary parameter is the fixed-field prime. These definitions specify
three independent obligations; they do not assert the classification.

The degree minimum and conjugate-generation estimates reduce the parameter
to three or five. At five, four conjugates give binary degree at most 24;
the separate outer-involution calculation then excludes outer actors. Inner
actors have rank at most two and contradict the degree minimum.

Sources: Aschbacher–Smith K.2, printed p.453; Guralnick–Malle,
*Classification of 2F-modules I*, §2 and Proposition 4.3, manuscript pp.4,
10–11. In particular the five-parameter calculation must retain outer actors
and all central covers. No PSU₄ or full-linear-normalizer assertion is made.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion

universe u v

/-- The literal K.2 source hypotheses, with no ratio or classification output. -/
structure SourceHypotheses {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) (p : ℕ) : Prop where
  sqtk : IsSQTK KnownSimple.IsKnownSimple G
  fitting : generalizedFitting G = L
  faithful : Function.Injective ρ
  irreducible : IsIrreducible (ρ.comp L.subtype)
  prime : p.Prime
  odd : Odd p
  quotient : ClassicalGroup.IsPSU (L ⧸ center L) 3 p

/-- The cross-characteristic degree minimum on the source domain, before any
offender hypothesis. The SQTK and F* hypotheses remain available to its proof. -/
def PrimeDegreeBound : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [IsQuasisimple L]
    {p : ℕ}, SourceHypotheses ρ L p → 3 < p →
      p * (p - 1) ≤ Module.finrank (ZMod 2) V

/-- Five conjugates suffice above parameter three; four suffice at five.
The generated subgroup must contain the actual central cover L. -/
def SourceConjugateBounds : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [IsQuasisimple L]
    {p : ℕ}, SourceHypotheses ρ L p → 3 < p →
      (∀ t : G, t ≠ 1 → t ^ 2 = 1 →
        ∃ g : Fin 5 → G, L ≤ closure (Set.range fun i => g i * t * (g i)⁻¹)) ∧
      (p = 5 → ∀ t : G, t ≠ 1 → t ^ 2 = 1 →
        ∃ g : Fin 4 → G, L ≤ closure (Set.range fun i => g i * t * (g i)⁻¹))

/-- The PSU₃(5) small-degree outer-involution estimate, without an offender
or a desired parameter conclusion among its hypotheses. -/
def SourceFiveOuterDisplacement : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [IsQuasisimple L],
    SourceHypotheses ρ L 5 → 20 ≤ Module.finrank (ZMod 2) V →
      Module.finrank (ZMod 2) V ≤ 24 →
      ∀ t : G, t ∉ L → t ^ 2 = 1 → 7 ≤ fixedCodim ρ (zpowers t)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
