module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.Small
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRemainingRadicals

/-!
# The original Sylow radical in the alternating-six source

The original source supplies a Sylow subgroup of `I`, whose ambient image is
`d.S`, and the equality `I = c.L ⊔ d.S`. Thus the literal small MS pair has a
Sylow radical in exactly its own ambient join. This assertion concerns the
original radical, not a later characteristic replacement.

For the exceptional alternating-six branch, the already proved plane radical
has even index 270 and cannot be this Sylow subgroup. Applying that exclusion
on the original cubic projection leaves full-core exhaustion or the Borel
branch. The projection retains kernel `extensionKernel`, including its odd
quotient over the two-core, and both full moving covers remain in the result.
The Borel contradiction and the natural reconstruction remain independent
proof obligations; this module does not establish either reconstruction.

Source: Aschbacher--Smith 15.3.26--31 and C.1.31--32; Meierfrankenfeld--
Stellmacher, *Pushing up weak BN-pairs of rank two* (1993), Section 5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension MarkedMS
open AlternatingSixReconstruction.Exceptional
open AlternatingSixReconstruction.Exceptional.Exhaustion
open AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G]
  {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
  (s : SourceData KnownSimple.IsKnownSimple d c)

include s

/-- The Sylow assertion on exactly the ambient join of the original MS pair. -/
theorem source_smallMSPair_original_sylow :
    Chapter1.IsSylowIn 2 d.S (c.L ⊔ d.S) := by
  rw [← s.generated]
  exact ⟨s.sylow, s.sylow_eq⟩

/-- The same original Sylow witness, on the literal cubic edge carrier. -/
theorem source_smallMSPair_original_sylow_edge :
    ∃ P : Sylow 2 (c.L ⊔ d.S : Subgroup G),
      (P : Subgroup (c.L ⊔ d.S : Subgroup G)) = edge c.L d.S := by
  obtain ⟨P, hP⟩ := source_smallMSPair_original_sylow s
  refine ⟨P, ?_⟩
  apply map_injective (c.L ⊔ d.S).subtype_injective
  exact hP.trans (map_subgroupOf_eq_of_le le_sup_right).symm

variable (hm : Parabolics.SmallParabolicMarking d I c.L)
  (e : CentralMarking c.L)
  (hz : Nat.card (center (c.L ⧸ pCore 2 c.L)) = 3)
local notation "hms" => source_smallMSPair s hm
local notation "Rg" => edge c.L d.S

/-- On the literal original source, the nonsylow plane alternative is impossible.
The remaining alternative uses the same cubic projection and both full covers. -/
theorem source_cubic_coreExhaustion_or_borel :
    CoreExhaustion c.L d.S ∨ ∃ hk : layerKernel c.L d.S = extensionKernel hms,
      Function.Surjective (CubicAction.projection hms e hz hk) ∧
      2 < sourceDistance hms ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection hms e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_plane_or_borel hms e hz with
    hex | ⟨hk, hs, hb, hcovers, u, hplane | hborel⟩
  · exact Or.inl hex
  · exact (plane_radical_not_sylow hms e hz hk u hplane
      (source_smallMSPair_original_sylow_edge s)).elim
  · exact Or.inr ⟨hk, hs, hb, hcovers, u, hborel⟩

/-- The full-core result feeds the actual C.1.32 consumer on `c.L,d.S`.
This remains conditional on excluding the original cubic Borel branch. -/
theorem source_cubic_rankTwo_or_borel :
    RankTwoAlternatives c.L d.S ∨ ∃ hk : layerKernel c.L d.S = extensionKernel hms,
      Function.Surjective (CubicAction.projection hms e hz hk) ∧
      2 < sourceDistance hms ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection hms e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (source_cubic_coreExhaustion_or_borel s hm e hz).imp
    (rankTwo_of_exhaustion hms e hz) id

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
