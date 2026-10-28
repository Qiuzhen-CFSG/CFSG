module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourTerminal

/-!
# Removing the original Borel and Sylow alternatives

The completed Borel terminal argument derives distance four from the
original source and recognizes the moving quotient through the actual
even cover, with kernel Q and cubic center retained. Its terminal theorem
has no original-Sylow or distance hypothesis. Applying it to the original
radical classification leaves exactly the plane image.

Consequently the cubic-kernel branch has radical index 270 and the
original radical cannot be Sylow. The whole-core reduction below retains
the same original projection and both full moving covers; only the plane
distance contradiction remains for its assembly consumer.

Source: MS93 (5.11)--(5.12), pp.923--926; Aschbacher--Smith C.1.31--32.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open Stellmacher.PushingUp.AmalgamGraph
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- The original Borel image is impossible at every source distance.
The terminal source theorem derives its distance-four premise internally. -/
theorem borel_image_impossible (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) : False :=
  OriginalSylow.borel_four_impossible h e hz hk u hR

include h e hz hk in
/-- Every original cubic radical has the literal plane image; neither
the point-core nor Borel branch needs an additional exclusion hypothesis. -/
theorem radical_image_eq_plane :
    ∃ u : S, (Rg).map π = D.map (MulAut.conj u).toMonoidHom := by
  obtain ⟨u, hp | hd | hb⟩ := radical_image_cases h e hz hk
  · exact (point_image_impossible h e hz hk u hp.le).elim
  · exact ⟨u, hd⟩
  · exact (borel_image_impossible h e hz hk u hb).elim

include h e hz hk in
/-- The remaining original radical has index 270, retaining E/Q of order three. -/
theorem cubic_radical_index_eq : (Rg).index = 270 := by
  obtain ⟨u, hu⟩ := radical_image_eq_plane h e hz hk
  exact plane_radical_index h e hz hk u hu

include h e hz hk in
/-- The original radical is not Sylow in the cubic initial-kernel branch. -/
theorem cubic_radical_not_sylow :
    ¬ ∃ P : Sylow 2 M, (P : Subgroup M) = Rg := by
  obtain ⟨u, hu⟩ := radical_image_eq_plane h e hz hk
  exact plane_radical_not_sylow h e hz hk u hu

include h e hz hk in
/-- The same exclusion in the unchanged original relative Sylow predicate. -/
theorem cubic_original_radical_not_sylow :
    ¬ Chapter1.IsSylowIn 2 R (L ⊔ R) := by
  rintro ⟨P, hP⟩
  apply cubic_radical_not_sylow h e hz hk
  refine ⟨P, ?_⟩
  apply map_injective (L ⊔ R).subtype_injective
  exact hP.trans (map_subgroupOf_eq_of_le le_sup_right).symm

omit hk in
include h e hz in
/-- Whole-core assembly has only the actual plane radical left, with the
original cubic kernel, surjective natural projection, and both full covers. -/
theorem coreExhaustion_or_cubic_plane :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S, (Rg).map (CubicAction.projection h e hz hk) =
        D.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_plane_or_borel h e hz with
    hx | ⟨hk, hs, hb, hcovers, u, hp | hB⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk, hs, hb, hcovers, u, hp⟩
  · exact (borel_image_impossible h e hz hk u hB).elim

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
