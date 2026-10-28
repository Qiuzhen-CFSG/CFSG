module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.Borel

/-!
# Original-Sylow reduction with generating Borel edges

The original Sylow hypothesis removes the plane image. In the remaining
Borel image, every original critical path has an incident edge generating
with its opposite seed. For a small critical image this edge necessarily
moves the entire critical kernel. No identification with a replacement
graph or reduction of the cubic kernel to the two-core is used.

These are conclusions in the surviving branch, not additional source
hypotheses. The shifted-path estimates and the distance-four and larger-
distance contradictions of MS93 (5.11)--(5.12) remain necessary to establish
whole-core exhaustion. This module does not assert that exhaustion.

Source: Aschbacher--Smith C.1.31--32, pp.135--136; Meierfrankenfeld--
Stellmacher (1993), (5.5)--(5.8), pp.915--920.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R)
  (hSyl : Chapter1.IsSylowIn 2 R (L ⊔ R)) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
local notation "Rg" => edge L R

include hSyl in
/-- The original Sylow reduction retains both full covers and supplies an
actual generating edge for every critical path of its surviving Borel case.
In the small-image case that same edge moves the full critical kernel. -/
theorem coreExhaustion_or_borel_generating_edges :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∧
        ∀ a z : Vertex Rg, ∀ _p : CriticalPath Rg (sourceGeometry h) a z,
          ∃ t, Adjacent Rg a t ∧ Q Rg t ⊔ Z Rg z = stabilizer Rg a ∧
            ((Q Rg z).relIndex (Z Rg a) < 4 →
              ¬ Q Rg t ≤ normalizer
                ((Z Rg a ⊓ Q Rg z : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))) := by
  rcases coreExhaustion_or_cubic_plane_or_borel h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hplane | hborel⟩
  · exact Or.inl hex
  · obtain ⟨P,hP⟩ := hSyl
    apply (plane_radical_not_sylow h e hz hk u hplane ?_).elim
    refine ⟨P,?_⟩
    apply map_injective (L ⊔ R).subtype_injective
    exact hP.trans (map_subgroupOf_eq_of_le le_sup_right).symm
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,hborel,?_⟩
    intro a z p
    obtain ⟨t,hat,hgen⟩ := borel_critical_generating_neighbor h e hz hk u hborel p
    exact ⟨t,hat,hgen,fun hsmall =>
      generating_edge_not_normalizes_kernel h e hz hk p hsmall hgen⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
