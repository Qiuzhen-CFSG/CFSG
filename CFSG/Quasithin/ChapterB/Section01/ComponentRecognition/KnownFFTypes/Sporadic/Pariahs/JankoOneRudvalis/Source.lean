module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs.JankoOneRudvalis
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.Representation.CharacteristicTwoIrreducibleRank
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.CubicNormalizerDegree

/-!
# J₁ and Rudvalis geometry under the Chapter K hypotheses

For the actual ambient group and its literal representation, conjugation on
the irreducible normal component bounds the ambient two-rank by the component's
automorphism two-rank. The supplied central quotient equivalence identifies
that component with a cover of the actual J₁ or Rudvalis carrier. Its
three-conjugate geometry acts on the same vector space. Applying the cubic
degree theorem to the original ambient action gives windows of eighteen and
thirty-six, respectively; classification inside those windows is separate.

Source: Aschbacher–Smith, K.1–K.4, printed pp.451–460. The source hypotheses
are retained explicitly, including the full known-simple catalogue. The
geometry itself holds without the SQTK or cubic-ratio restrictions; neither
restriction is imposed on the full linear normalizer.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs
open Subgroup Theory.GroupTheory Representation.BinaryOffender

/-- The actual Chapter K actor has two-rank at most three in the J₁ case;
its component action has three-conjugate geometry on the literal module. -/
theorem j1_source_geometry
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (_hG : IsSQTK KnownSimple.IsKnownSimple G)
    [IsQuasisimple (generalizedFitting G)]
    (hf : Function.Injective ρ)
    (hi : Representation.IsIrreducible (ρ.comp (generalizedFitting G).subtype))
    (_hq : cubicRatio ρ ≤ 2)
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* Janko1.Model) :
    primeRank 2 G ≤ 3 ∧
      NormalizerThreeConjugates (ρ.comp (generalizedFitting G).subtype) := by
  let := hi
  obtain ⟨hgen, hrank⟩ := j1_centralCover_geometry
    (ρ.comp (generalizedFitting G).subtype)
    (hf.comp (generalizedFitting G).subtype_injective) hi e
  exact ⟨(Representation.CharacteristicTwoIrreducible.primeRank_le_automorphisms
    ρ (generalizedFitting G) hf).trans hrank, hgen⟩

/-- The actual Chapter K actor has two-rank at most six in the Rudvalis case;
its original component representation has three-conjugate geometry. -/
theorem ru_source_geometry
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (_hG : IsSQTK KnownSimple.IsKnownSimple G)
    [IsQuasisimple (generalizedFitting G)]
    (hf : Function.Injective ρ)
    (hi : Representation.IsIrreducible (ρ.comp (generalizedFitting G).subtype))
    (_hq : cubicRatio ρ ≤ 2)
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* Rudvalis.Model) :
    primeRank 2 G ≤ 6 ∧
      NormalizerThreeConjugates (ρ.comp (generalizedFitting G).subtype) := by
  let := hi
  obtain ⟨hgen, hrank⟩ := ru_centralCover_geometry
    (ρ.comp (generalizedFitting G).subtype)
    (hf.comp (generalizedFitting G).subtype_injective) hi e
  exact ⟨(Representation.CharacteristicTwoIrreducible.primeRank_le_automorphisms
    ρ (generalizedFitting G) hf).trans hrank, hgen⟩

/-- Apply the J₁ geometry to the literal Chapter K representation: its cubic
ratio bounds displacement by twice the actor rank, giving degree at most 18. -/
theorem j1_source_degree_le_eighteen
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (_hG : IsSQTK KnownSimple.IsKnownSimple G)
    [IsQuasisimple (generalizedFitting G)]
    (hf : Function.Injective ρ)
    (hi : Representation.IsIrreducible (ρ.comp (generalizedFitting G).subtype))
    (hq : cubicRatio ρ ≤ 2)
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* Janko1.Model) :
    Module.finrank (ZMod 2) V ≤ 18 := by
  let : IsSimpleGroup (generalizedFitting G ⧸ center (generalizedFitting G)) :=
    IsQuasisimple.simple
  let : IsSimpleGroup Janko1.Model := e.symm.isSimpleGroup
  exact finrank_le_six_mul_of_cubic_central_quotient ρ (generalizedFitting G)
    hf hi e j1_threeConjugateAutomorphisms
    ChapterG.Section07.SporadicLocal.j1_automorphism_twoRank_le_three hq

/-- The Rudvalis geometry bounds the degree of the actual Chapter K module
by 36, including arbitrary central covers and permissible ambient actions. -/
theorem ru_source_degree_le_thirtySix
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (_hG : IsSQTK KnownSimple.IsKnownSimple G)
    [IsQuasisimple (generalizedFitting G)]
    (hf : Function.Injective ρ)
    (hi : Representation.IsIrreducible (ρ.comp (generalizedFitting G).subtype))
    (hq : cubicRatio ρ ≤ 2)
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* Rudvalis.Model) :
    Module.finrank (ZMod 2) V ≤ 36 := by
  let : IsSimpleGroup (generalizedFitting G ⧸ center (generalizedFitting G)) :=
    IsQuasisimple.simple
  let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
  let : Group.IsPerfect Rudvalis.Model :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact finrank_le_six_mul_of_cubic_central_quotient ρ (generalizedFitting G)
    hf hi e ru_threeConjugateAutomorphisms
    ChapterG.Section07.SporadicLocal.ru_automorphism_twoRank_le_six hq

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs
