module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.OriginalFieldFourImage
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.OriginalDistance
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.FieldFour

/-!
# Field-four recognition on the actual nonabelian Chapter11 source

The original point core acts through a cubic point radical, so its marked
intersection with L cannot be a full symplectic Sylow subgroup. Its original
nonabelian closure supplies a characteristic replacement of distance two.
The completed nonsylow field theorem therefore applies to the literal
MS input in L O₂(G₁), and subgroup transport returns the block on L.

The original field, marked quotient and complete chosen module are retained.
No endgame witness, nonsylow premise or distance callback is supplied.
Source: Aschbacher--Smith 11.5.7 and C.1.32; MS93 (3.7), pp.876--877.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
open Subgroup Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open ChapterC.RankTwo.NonbinarySymplectic
open ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D) (m : MarkedFlag E)

/-- Restriction to the literal MS product preserves the original marked
point-core image, on every representative. -/
theorem intrinsicMSInput_radical_marked_image
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2)) :
    (((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)).subgroupOf
      (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))).map
        (componentProjection (intrinsicMSInput E m hms)) =
      PointModel.image m (E.G₁.pCoreIn 2) := by
  let J := L ⊔ E.G₁.pCoreIn 2
  let e : L.subgroupOf J ≃* L := subgroupOfEquivOfLe le_sup_left
  have he (l : L.subgroupOf J) :
      componentProjection (intrinsicMSInput E m hms) l = PointModel.quotientMap m (e l) :=
    intrinsicMSInput_quotient_mk E m hms l
  ext x
  constructor
  · rintro ⟨l,hl,rfl⟩
    exact ⟨e l,hl,(he l).symm⟩
  · rintro ⟨l,hl,rfl⟩
    refine ⟨e.symm l,hl,?_⟩
    exact (he (e.symm l)).trans (congrArg (PointModel.quotientMap m) (e.apply_symm_apply l))

/-- The actual nonabelian closure forces field degree two and an Sp₄(4)
block on the original L. Both the nonsylow and distance hypotheses are
discharged from the source geometry. -/
theorem msPair_field_and_block_of_nonabelian
    (g : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (hne : ¬ IsMulCommutative E.W) :
    E.input.field.degree=2 ∧ Nat.card E.input.field.Carrier=4 ∧ ChapterC.IsSp4FourBlock L := by
  obtain ⟨d,graph,hb⟩ := msPair_distance_two_of_nonabelian E m g hp hms hne
  have hnsyl : ¬ ∃ S : Sylow 2 (Sp E.input.field.Carrier), (S : Subgroup _) =
      (((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)).subgroupOf
        (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))).map
          (componentProjection (intrinsicMSInput E m hms)) := by
    rw [intrinsicMSInput_radical_marked_image E m hms]
    exact original_core_marked_image_not_sylow E m g hp
  obtain ⟨hn,hF,hblock⟩ := OriginalStar.original_nonsylow_distance_two_field_and_block
    (intrinsicMSInput E m hms) d graph hb hnsyl
  let e : L.subgroupOf (L ⊔ E.G₁.pCoreIn 2) ≃* L := subgroupOfEquivOfLe le_sup_left
  obtain ⟨hs,F,hfield,hfinite,hcard,ρ,⟨model⟩,haction⟩ := hblock
  exact ⟨hn,hF,hs.of_mulEquiv e,F,hfield,hfinite,hcard,ρ,⟨model.comap e.symm⟩,haction⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
