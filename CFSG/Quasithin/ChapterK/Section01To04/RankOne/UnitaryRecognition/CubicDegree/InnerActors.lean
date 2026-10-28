module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.CubicDegree.Reduction
public import Theory.Representation.SU3.CubicDegree.InnerActors.Assembly

/-!
# The source inner-actor degree bound

Apply the inner-actor reduction to the original binary action inflated along
the specified surjective SU₃ central cover. Its kernel is exactly the covering
kernel, and irreducibility is preserved. The elementary actor remains the
literal subgroup of the full linear normalizer of this inflated action.

The concrete root-control and three-center generation theorems discharge
both group-geometric premises, proving the inner branch without a module
catalogue or a faithfulness assumption on the inflated action. The original
conditional interface remains available. The complete cubic degree theorem,
including the other actor branches, is owned by `CubicDegree`.

Source: Aschbacher--Smith K.3.3, printed p.456, under the hypotheses on
p.451; Guralnick--Malle II, Lemma 2.1 and Theorem 4.10/Table 7.
-/

public section
open BenderSuzuki.MatrixGroups Representation Representation.BinaryOffender Subgroup
open Representation.SU3.CubicDegree.InnerActors
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree

/-- The actual source cover satisfies every representation premise of the
root-geometric reduction. Only the two group inputs remain to be supplied. -/
theorem source_degree_le_of_inner_actor_of_root_geometry
    {F V G : Type*} [Field F] [Finite F] [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (J : HermitianForm 3 F) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (hr : RootControl J.specialSubgroup s) (hg : ThreeRootGeneration J.specialSubgroup)
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
    (h : SourceHypotheses ρ L) (π : J.specialSubgroup →* L)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center J.specialSubgroup)
    (A : Subgroup (linearNormalizer ((ρ.comp L.subtype).comp π)))
    (hA : IsElementaryTwo A)
    (hc : fixedCodim (normalizerRepresentation ((ρ.comp L.subtype).comp π)) A ≤
      2 * rank A)
    (hinner : A ≤ (actionImage ((ρ.comp L.subtype).comp π)).subgroupOf
      (linearNormalizer ((ρ.comp L.subtype).comp π))) :
    Module.finrank (ZMod 2) V ≤ 6 * s := by
  have hk : ((ρ.comp L.subtype).comp π).ker ≤ center J.specialSubgroup := by
    rw [pullback_ker_eq J h π]
    exact hker
  exact finrank_le_of_inner_actor_of_root_geometry J hs hcard hconj hr hg
    ((ρ.comp L.subtype).comp π) (pullback_irreducible J h π hπ) hk A hA hc hinner

/-- The inner branch for the actual source action inflated along its specified
surjective central SU₃ cover. The root geometry is fully discharged; cubicity
is unnecessary once the elementary actor lies in the action image. -/
theorem source_degree_le_of_inner_actor
    {F V G : Type*} [Field F] [Finite F] [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (J : HermitianForm 3 F) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
    (h : SourceHypotheses ρ L) (π : J.specialSubgroup →* L)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center J.specialSubgroup)
    (A : Subgroup (linearNormalizer ((ρ.comp L.subtype).comp π)))
    (hA : IsElementaryTwo A)
    (hc : fixedCodim (normalizerRepresentation ((ρ.comp L.subtype).comp π)) A ≤
      2 * rank A)
    (hinner : A ≤ (actionImage ((ρ.comp L.subtype).comp π)).subgroupOf
      (linearNormalizer ((ρ.comp L.subtype).comp π))) :
    Module.finrank (ZMod 2) V ≤ 6 * s := by
  have hk : ((ρ.comp L.subtype).comp π).ker ≤ center J.specialSubgroup := by
    rw [pullback_ker_eq J h π]
    exact hker
  exact finrank_le_of_inner_actor J hs hcard hconj
    ((ρ.comp L.subtype).comp π) (pullback_irreducible J h π hπ) hk A hA hc hinner

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree
