module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.Geometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.FiveCensus
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.InnerGeometry

/-!
# Native subcompletions in the original unitary normalizer pair

The full DGS realization supplies the compatible original normalizer maps.
Their native images generate a normal subgroup of the normalizer join and
have the entire native overlap. In U₄ the proved order equality makes the
join all of G; original simplicity then makes the native images generate G.
This gives an actual completion of the native projective amalgam in G with
its literal inherited maps, without asserting PSU recognition. In U₅ the
normal subgroup acts transitively on both types of the original full graph,
retaining the prepared n = 4 and the 65/17 geometry.

Source: Aschbacher–Smith 5.3.1–4, F.4.3,13,17, pp.658–659,274,280,282–283.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
open ChapterF.SourceCompletion.UnitaryNonbinary UnitaryCompletion

namespace UnitaryCompletion
variable {G : Type*} [Group G] {L K : Subgroup G}
variable {B : Type*} [Group B] {P₀ P₁ : Subgroup B}
variable (E : SourceExtension P₀ P₁)

/-- Once the original join is all of G, include the same endpoint maps
into G. No new marking or unrelated endpoint equivalence is introduced. -/
def ambientCompletion
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := NormalizerJoin L K))
    (ht : NormalizerJoin L K = ⊤) :
    RankTwoAmalgam.FaithfulCompletion E.amalgam (G := G) where
  left := (NormalizerJoin L K).subtype.comp c.left
  right := (NormalizerJoin L K).subtype.comp c.right
  compatible := by
    ext d
    exact congrArg Subtype.val (DFunLike.congr_fun c.compatible d)
  left_injective := (NormalizerJoin L K).subtype_injective.comp c.left_injective
  right_injective := (NormalizerJoin L K).subtype_injective.comp c.right_injective
  middle_injective := (NormalizerJoin L K).subtype_injective.comp c.middle_injective
  generated := by
    rw [← MonoidHom.map_range, ← MonoidHom.map_range, ← Subgroup.map_sup,
      c.generated, ← MonoidHom.range_eq_map, range_subtype,ht]

theorem ambientCompletion_overlap
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := NormalizerJoin L K))
    (ht : NormalizerJoin L K = ⊤)
    (ho : c.left.range ⊓ c.right.range = c.middle.range) :
    (ambientCompletion E c ht).left.range ⊓ (ambientCompletion E c ht).right.range =
      (ambientCompletion E c ht).middle.range := by
  have he := congrArg (fun N : Subgroup (NormalizerJoin L K) =>
    N.map (NormalizerJoin L K).subtype) ho
  rw [Subgroup.map_inf _ _ _ (NormalizerJoin L K).subtype_injective,
    MonoidHom.map_range, MonoidHom.map_range, MonoidHom.map_range] at he
  exact he
end UnitaryCompletion

private theorem four_point_nontrivial (m : ℕ) (hm : 1 ≤ m) :
    Nontrivial (ChapterF.GreenBook.LieModels.UnitaryFour.pointParabolic m hm) := by
  open ChapterF.GreenBook.LieModels.UnitaryFour in
  let : Finite (ProjectiveGroup m hm) := Finite.of_surjective (projection m hm)
    (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project_surjective _ _)
  apply Finite.one_lt_card_iff_nontrivial.mp
  have hd := ((ChapterF.GreenBook.LieModels.UnitaryFour.planeParabolic m hm).subgroupOf
    (ChapterF.GreenBook.LieModels.UnitaryFour.pointParabolic m hm)).index_dvd_card
  have hi := four_local_index m hm false
  change ((ChapterF.GreenBook.LieModels.UnitaryFour.planeParabolic m hm).subgroupOf
    (ChapterF.GreenBook.LieModels.UnitaryFour.pointParabolic m hm)).index = 2^m+1 at hi
  rw [hi] at hd
  have hc := Nat.le_of_dvd (Nat.card_pos (α :=
    ChapterF.GreenBook.LieModels.UnitaryFour.pointParabolic m hm)) hd
  have hp : 0 < 2^m := by positivity
  change 2^m+1 ≤ _ at hc
  omega

/-- The native U₄ projective endpoint maps generate the original simple G.
This is an actual native amalgam completion, not yet its recognition. -/
theorem Preparation.unitary_native_ambient_completion
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (E : FourExtension m hm) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    1 < m ∧ n = 2*m ∧ ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := G),
      c.left.range ⊓ c.right.range = c.middle.range ∧ E.innerGenerated c = ⊤ ∧
      ∃ b : RankTwoAmalgam.FaithfulCompletion
          (SourceExtension.nativeAmalgam
            (P₀ := ChapterF.GreenBook.LieModels.UnitaryFour.pointParabolic m hm)
            (P₁ := ChapterF.GreenBook.LieModels.UnitaryFour.planeParabolic m hm)) (G := G),
        b.left = E.innerLeft c ∧ b.right = E.innerRight c ∧
        b.left.range ⊓ b.right.range = b.middle.range := by
  obtain ⟨hmgt,hn,c,ho,hcard,_⟩ := d.unitary_completion_input h hH hp m hm hc E he horder
  have ht := normalizerJoin_eq_top_of_card L (residual H) E horder
    (four_completion_card_eq m hm hmgt E c ho hcard)
  let cG := ambientCompletion E c ht
  have hoG := ambientCompletion_overlap E c ht ho
  let : IsSimpleGroup G := h.qtke.simple
  let : Nontrivial (ChapterF.GreenBook.LieModels.UnitaryFour.pointParabolic m hm) :=
    four_point_nontrivial m hm
  have hN := E.innerGenerated_eq_top_of_simple cG (four_conj_injective m hm)
  exact ⟨hmgt,hn,cG,hoG,hN,E.nativeCompletionOfTop cG (four_conj_injective m hm) hN,
    rfl,rfl,E.nativeCompletionOfTop_overlap cG (four_conj_injective m hm) hN hoG⟩

/-- The fixed U₅(4) branch has a normal faithful native subcompletion
acting on both original full-extension vertex orbits, with n = 4 retained. -/
theorem Preparation.unitaryFive_normal_native_completion
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : FiveLocalComparison L (residual H) (sourceS L H) U)
    (E : FiveExtension U) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    n = 4 ∧ ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
        (G := NormalizerJoin L (residual H)),
      c.left.range ⊓ c.right.range = c.middle.range ∧
      (E.innerGenerated c).Normal ∧
      (E.innerCompletion c (five_conj_injective U)).left.range ⊓
        (E.innerCompletion c (five_conj_injective U)).right.range =
        (E.innerCompletion c (five_conj_injective U)).middle.range ∧
      (∀ v : Vertex c.cosetFamily, ∃ a : E.innerGenerated c,
        a.val • base c.cosetFamily v.type = v) ∧
      (∀ v : Vertex (E.innerFamily c),
        Nat.card ((Subgroup.CosetGeometry.RankTwo.graph (E.innerFamily c)).neighborSet v) =
          fiveDegree v.type) ∧
      (E.innerGenerated c).index ∣ E.nativeOverlap.index := by
  obtain ⟨hn,c,ho,_⟩ := d.unitaryFive_completion_census h hH hp U hc E he horder
  exact ⟨hn,c,ho,five_completion_normal_native U E c ho⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
