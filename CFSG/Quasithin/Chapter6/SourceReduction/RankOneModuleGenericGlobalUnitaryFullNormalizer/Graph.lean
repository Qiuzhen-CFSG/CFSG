module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFullNormalizer.Four
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryNativeLift.Graph

/-!
# The graph involution in the chosen full-normalizer realization

The original graph element lies in T and outside L. Since T intersects the
reduced overlap in T ∩ L, this element is outside the reduced overlap for
every marking. Apply the full inner-preimage theorem to the very action and
lift retained by the chosen extension. Its full middle isomorphism preserves
the element's order and identifies its image with that same native lift.
No change of the chosen extension or action is needed.

Source: the degree-two case of Aschbacher–Smith 5.3.2 and F.4.37,
printed pp.659 and293.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
open ChapterF.SourceCompletion.UnitaryNonbinary UnitaryCompletion
variable {G : Type*} [Group G]

/-- Every marked realization preserves an involution outside the reduced overlap
as an outer involution, with the same action and endpoint maps. -/
theorem UnitaryFourNormalizerMarking.outer_involution
    {L K S : Subgroup G} {m : ℕ} {hm : 1 ≤ m}
    (M : UnitaryFourNormalizerMarking L K S m hm)
    (g : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G))
    (ho : orderOf g.val = 2)
    (hout : g.val ∉ ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1) :
    (∃ a : UnitarySource.MarkedMiddleAction L K S (amalgam m hm),
      ∃ f : UnitaryNativeLift.Four.Lift m hm a,
      ∃ F : RankTwoAmalgam.Iso (normalizerDiagram L K) M.extension.amalgam,
      (∀ x, (F.left (inclusion M.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
      (∀ x, (F.right (inclusion M.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
      (∀ z, (F.middle z).val = (f.action z).val) ∧
      orderOf (F.middle g) = 2 ∧ (F.middle g).val ∉ inner (ProjectiveGroup m hm)) ∨
    (∃ a : UnitarySource.MarkedMiddleAction L K S (amalgam m hm).reverse,
      ∃ f : UnitaryNativeLift.Four.LiftReverse m hm a,
      ∃ F : RankTwoAmalgam.Iso (normalizerDiagram L K) M.extension.amalgam.reverse,
      (∀ x, (F.left (inclusion M.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
      (∀ x, (F.right (inclusion M.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
      (∀ z, (F.middle z).val = (f.action z).val) ∧
      orderOf (F.middle g) = 2 ∧ (F.middle g).val ∉ inner (ProjectiveGroup m hm)) := by
  have hg : orderOf g = 2 :=
    (orderOf_injective _ (normalizer (L : Set G) ⊓ normalizer (K : Set G)).subtype_injective g).symm.trans ho
  rcases M.marking with ⟨a,f,F,hFl,hFr,hFm,_⟩ | ⟨a,f,F,hFl,hFr,hFm,_⟩
  · refine Or.inl ⟨a,f,F,hFl,hFr,hFm,(orderOf_injective F.middle.toMonoidHom F.middle.injective g).trans hg,?_⟩
    have he : (F.middle g).val = (f.action g).val := hFm g
    exact fun h => hout ((UnitaryFullNormalizer.four_inner_preimage f g).mp (he ▸ h))
  · refine Or.inr ⟨a,f,F,hFl,hFr,hFm,(orderOf_injective F.middle.toMonoidHom F.middle.injective g).trans hg,?_⟩
    have he : (F.middle g).val = (f.action g).val := hFm g
    exact fun h => hout ((UnitaryFullNormalizer.four_inner_preimage_reverse f g).mp (he ▸ h))

variable [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The original graph element survives in the same named extension used by
ambient order and recognition, with all endpoint and whole-middle markings. -/
theorem Preparation.unitaryFour_constructed_graph
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    let M := d.unitaryFourNormalizerMarking h hH hp m hm (Or.inr hc)
    1 < m ∧ n = 2*m ∧ ∃ g : G,
      g ∈ sourceS L H ∧ g ∈ (T : Subgroup G) ∧ orderOf g = 2 ∧
      g ∉ L ∧ g ∉ residual H ∧
      ∃ hg : g ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G),
      (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) (amalgam m hm),
        ∃ f : UnitaryNativeLift.Four.Lift m hm a,
        ∃ F : RankTwoAmalgam.Iso (normalizerDiagram L (residual H)) M.extension.amalgam,
        (∀ x, (F.left (inclusion M.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
        (∀ x, (F.right (inclusion M.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
        (∀ z, (F.middle z).val = (f.action z).val) ∧
        orderOf (F.middle ⟨g,hg⟩) = 2 ∧ (F.middle ⟨g,hg⟩).val ∉ inner (ProjectiveGroup m hm)) ∨
      (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) (amalgam m hm).reverse,
        ∃ f : UnitaryNativeLift.Four.LiftReverse m hm a,
        ∃ F : RankTwoAmalgam.Iso (normalizerDiagram L (residual H)) M.extension.amalgam.reverse,
        (∀ x, (F.left (inclusion M.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
        (∀ x, (F.right (inclusion M.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
        (∀ z, (F.middle z).val = (f.action z).val) ∧
        orderOf (F.middle ⟨g,hg⟩) = 2 ∧ (F.middle ⟨g,hg⟩).val ∉ inner (ProjectiveGroup m hm)) := by
  obtain ⟨hmgt,hn,g,hgs,hgt,hgo,hgl,hgk,hg,_⟩ :=
    d.unitary_graph_native_lifted_middle_action h hH hp m hm hc
  refine ⟨hmgt,hn,g,hgs,hgt,hgo,hgl,hgk,hg,?_⟩
  apply (d.unitaryFourNormalizerMarking h hH hp m hm (Or.inr hc)).outer_involution ⟨g,hg⟩ hgo
  intro hgC
  have hh := (d.unitary_reduced_overlap_sylow h hH hp m hm (Or.inr hc)).le ⟨hgt,hgC⟩
  exact hgl hh.2

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
