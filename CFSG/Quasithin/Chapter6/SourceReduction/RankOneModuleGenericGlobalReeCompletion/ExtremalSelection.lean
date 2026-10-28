module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.RootExhaustion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.ShortAmbient

/-!
# The original Ree short marker with exhaustion and fusion discharged

The coordinate exhaustion of native involutions and the full endpoint fusion
comparison remove both earlier-source premises of the existing extremal
selection. All three centralizer Sylows, the literal local-centralizer map,
radical placement and long/short nonfusion refer to the same supplied marking.
This supplies F.4.40 to the separate F.4.42 ambient-containment argument.
Source: Aschbacher--Smith F.4.27,35,40--42, printed pp.288,292,294--295 of
`refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion
open ReeF4 ReeF4.Parabolics ReeF4.EvenInvolutionGeometry
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ)
  (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
include d h hH hp he

/-- The simultaneous short-marker extremality conclusion from the original
prepared inputs, with native exhaustion and full endpoint fusion proved. -/
theorem Preparation.ree_short_extremal_comparison_of_source
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m) :
    ∃ (t : Model m) (v : normalizer (L : Set G)),
      IsShortRootInvolution t ∧ t ∈ radical m .linear ∧
      v.val ∈ L.pCoreIn 2 ∧ v.val ∈ T ∧ orderOf v.val = 2 ∧
      D.leftToCarrier v = D.extension.baseHom t ∧
      ((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))).map
        D.leftToCarrier = centralizer ({D.extension.baseHom t} : Set D.extension.carrier) ∧
      (∃ R : Sylow 2 (centralizer ({v} : Set (normalizer (L : Set G)))),
        (R : Subgroup (centralizer ({v} : Set (normalizer (L : Set G))))) =
          ((T : Subgroup G).subgroupOf (normalizer (L : Set G))).subgroupOf
            (centralizer ({v} : Set (normalizer (L : Set G))))) ∧
      (∃ R : Sylow 2 (centralizer ({v.val} : Set G)),
        (R : Subgroup (centralizer ({v.val} : Set G))) =
          (T : Subgroup G).subgroupOf (centralizer ({v.val} : Set G))) ∧
      (∃ S : Sylow 2 D.extension.carrier,
        (S : Subgroup D.extension.carrier) =
          ((T : Subgroup G).subgroupOf (normalizer (L : Set G) ⊓
            normalizer (residual H : Set G))).map D.middleToCarrier ∧
        D.extension.baseHom t ∈ S ∧
        ∃ R : Sylow 2 (centralizer ({D.extension.baseHom t} : Set D.extension.carrier)),
          (R : Subgroup (centralizer ({D.extension.baseHom t} : Set D.extension.carrier))) =
            (S : Subgroup D.extension.carrier).subgroupOf
              (centralizer ({D.extension.baseHom t} : Set D.extension.carrier))) ∧
      3 ∣ Nat.card (solvableResidual (centralizer ({v.val} : Set G))) ∧
      ∀ z ∈ (center (residual H)).map (residual H).subtype,
        orderOf z = 2 → ¬ IsConj z v.val := by
  have hm := d.ree_parameter_positive h hp m 0 .linear D.pure.left
  exact d.ree_short_extremal_comparison h hH hp m he D
    (ReeF4.SourceCompletion.involution_root_classes m hm)
    (fun x y hx hy hxy =>
      (d.ree_left_involution_fusion_iff h hp m hH he D x y hx hy).mp hxy)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
