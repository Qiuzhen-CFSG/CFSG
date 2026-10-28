module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs.Geometry
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs.Transfer
public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Bounds
public import Theory.GroupTheory.PrimeRankCentralCover

/-!
# J₄ geometry for the Chapter K sporadic branch

The rank bound and generation theorem hold on the actual catalogue carrier.
The certified generating triples for the two literal ATLAS involutions `a`
and `(ababb)^5`, their class coverage and full innerness discharge every
generation premise. The resulting geometry transfers to arbitrary faithful
irreducible binary central covers, retaining the specified central quotient.

The historical module path is retained, but the required scope is J₄ only.
Source: Aschbacher–Smith, G.7.3(2), printed p.348, for the rank bound;
Revin–Zavarnitsine, https://arxiv.org/abs/2505.05173v2, Theorem 1, for generation.
The central-cover transfer consumes `SimpleGeometry` to bound the degree window
in Chapter K.4 (printed pp.457–460); excluding the modules in that window is a
separate obligation. No FF or cubic module classification is asserted here.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs
open Subgroup Theory.GroupTheory Representation.BinaryOffender
universe u v

/-- The automorphism rank bound on the literal known-simple J₄ carrier. -/
theorem j4_automorphism_twoRank_le_eleven
    [IsSimpleGroup KnownSimple.SporadicName.j4.Carrier]
    [Group.IsPerfect KnownSimple.SporadicName.j4.Carrier] :
    primeRank 2 (MulAut KnownSimple.SporadicName.j4.Carrier) ≤ 11 := by
  let : IsSimpleGroup Janko4.Model :=
    inferInstanceAs (IsSimpleGroup KnownSimple.SporadicName.j4.Carrier)
  let : Group.IsPerfect Janko4.Model :=
    inferInstanceAs (Group.IsPerfect KnownSimple.SporadicName.j4.Carrier)
  exact Janko4.TwoRank.automorphism_twoRank_le_eleven

/-- The two explicit representative triples suffice for all inherited simple
central quotients. Their construction remains with the concrete producers. -/
theorem j4_simpleGeometry_of_generating_representatives
    (hfirst : ThreeConjugatesGenerate Janko4.a)
    (hsecond : ThreeConjugatesGenerate
      ((Janko4.a * Janko4.b * Janko4.a * Janko4.b * Janko4.b) ^ 5)) :
    SimpleGeometry .j4 11 := by
  intro _ _ _
  let : IsSimpleGroup Janko4.Model :=
    inferInstanceAs (IsSimpleGroup KnownSimple.SporadicName.j4.Carrier)
  let : Group.IsPerfect Janko4.Model :=
    inferInstanceAs (Group.IsPerfect KnownSimple.SporadicName.j4.Carrier)
  exact ⟨Janko4.ThreeConjugates.automorphisms_of_representatives hfirst hsecond,
    j4_automorphism_twoRank_le_eleven⟩

/-- Every nonidentity involutory automorphism of the literal J₄ model has
three inner conjugates generating a subgroup containing all inner automorphisms. -/
theorem j4_threeConjugateAutomorphisms
    [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model] :
    ThreeConjugateAutomorphisms Janko4.Model :=
  Janko4.ThreeConjugates.automorphisms

/-- The J₄ simple-model geometry with both representative triples discharged. -/
theorem simpleGeometry_j4 : SimpleGeometry .j4 11 :=
  j4_simpleGeometry_of_generating_representatives
    Janko4.ThreeConjugates.first_three_conjugates_generate
    Janko4.ThreeConjugates.second_three_conjugates_generate

/-- J₄ geometry on every faithful irreducible binary central cover. -/
theorem geometry_j4 : Geometry.{u,v} .j4 11 :=
  geometry_of_simpleGeometry .j4 11 simpleGeometry_j4

/-- The actual cover's automorphism rank and generation in its literal linear
normalizer, transported through the given central quotient equivalence. -/
theorem j4_centralCover_geometry
    {L : Type u} {V : Type v} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) L V) (hf : Function.Injective ρ)
    (hi : ρ.IsIrreducible) (e : L ⧸ center L ≃* Janko4.Model) :
    NormalizerThreeConjugates ρ ∧ primeRank 2 (MulAut L) ≤ 11 := by
  obtain ⟨hgen, hrank⟩ := geometry_j4 ρ hf hi ⟨e⟩
  have hcover := automorphism_primeRank_le_quotient_center (E := L) 2
  rw [primeRank_equiv 2 (MulAut.congr e)] at hcover
  exact ⟨hgen, hcover.trans hrank⟩

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs
