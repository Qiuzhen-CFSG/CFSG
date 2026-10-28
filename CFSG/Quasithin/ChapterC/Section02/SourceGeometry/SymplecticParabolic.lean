module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.ChiZeroRank
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank

/-!
# The full symplectic parabolic in the original C.2.7 marking

The intrinsic marked-normalizer theorem allows either a full point or plane
parabolic, or a chi-zero block. The latter has cyclic Sylow three-subgroups,
and every quotient retains that property. The actual symplectic matrix group
has three-rank at least two, excluding that alternative. This supplies the
literal marked parabolic, including the Sp4(4) specialization used in 15.3.20.
It does not assert the separate field restriction to four elements.

Source: Aschbacher–Smith C.2.7(3), printed pp.146–147, and 15.3.20, p.1127.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}

/-- Quotients of an actual χ₀ block retain cyclic Sylow three-subgroups. -/
theorem chiZero_star_threeRank_le_one (hc : IsChiZeroBlock K) :
    primeRank 3 (starImage K R K) ≤ 1 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 K := Classical.choice inferInstance
  exact P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hc.threeRank_le_one)
    (toStarImage K R) (toStarImage_surjective K R)

/-- The symplectic row has cubic rank two, so the intrinsic χ₀ escape in
its marked-parabolic theorem cannot occur. -/
theorem star_symplectic_marked_parabolic_from_source
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : starImage K R K ≃* Sp F) (hq : 4 ≤ Nat.card F) :
    ∃ g : Sp F,
      (((starM K R M).subgroupOf (starImage K R K)).map e.toMonoidHom).map
          (MulAut.conj g).toMonoidHom = pointParabolic ∨
      (((starM K R M).subgroupOf (starImage K R K)).map e.toMonoidHom).map
          (MulAut.conj g).toMonoidHom = planeParabolic := by
  rcases star_symplectic_parabolic_or_chiZero_from_source h e hq with hp | ⟨_,hc⟩
  · exact hp
  · have hlow : 2 ≤ primeRank 3 (Sp F) :=
      Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans
        (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Sp F)).subtype
          (commutator (Sp F)).subtype_injective)
    have hhigh := chiZero_star_threeRank_le_one (R := R) hc
    rw [primeRank_congr 3 e] at hhigh
    omega

/-- The Sp₄(4) specialization is the literal parabolic predicate consumed
by original C.2.7 and source 15.3.20. -/
theorem star_sp4Four_parabolic_from_source
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : starImage K R K ≃* Sp F) (hF : Nat.card F = 4) :
    IsSp4FourMaximalParabolic ((starM K R M).subgroupOf (starImage K R K)) := by
  obtain ⟨g,hg⟩ := star_symplectic_marked_parabolic_from_source h e (by omega)
  refine ⟨F,inferInstance,inferInstance,hF,e.trans (MulAut.conj g),?_⟩
  have he : (e.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by ext x; rfl
  rw [he]
  simpa only [map_map] using hg
end CFSG.Quasithin.ChapterC.C27Source
