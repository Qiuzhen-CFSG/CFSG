module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.Thompson
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.ShortAmbient

/-!
# Ambient recognition of the prepared general Ree branch

The original preparation constructs the compatible full-normalizer marking.
Native exhaustion and the proved full-endpoint fusion discharge all extra
premises of the short-centralizer theorem. Its extremal marker retains the
original Sylow, the whole overlap and the same extension. The Thompson count
then gives equality with that full extension's order. The marked octagon/Weyl
recognizer proves ambient generation and uses original simplicity to remove
the odd outer part, yielding the actual native ReeF4 group.

Only the original preparation, generic input, HStar placement, perfect whole
residual and either compatible comparison orientation remain. The parameter
equation is the original n=2m+1, with every positive m, including q=8.
Exhaustive comparison selection and construction of the preparation stay with
the parent source assembly.
Source: Aschbacher--Smith 5.3.1--4, printed pp.658--659, and F.4.27,30,35,
40,42--44, printed pp.288--296 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion
open ReeF4 ReeF4.Parabolics ReeF4.EvenInvolutionGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The actual general Ree prepared row, at the original parameter. All
exhaustion, full endpoint fusion, short-centralizer containment, full-extension
order comparison and ambient recognition premises are discharged. -/
theorem Preparation.ree_ambient_recognition
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse)) :
    2*m+1 = n ∧ 0 < m ∧ Nonempty (G ≃* Model m) := by
  obtain ⟨hn,hm,⟨D⟩⟩ := d.ree_full_normalizer_marking h hH hp m he
  have hcross (x : normalizer (L : Set G)) (y : normalizer (residual H : Set G))
      (hx : orderOf x.val = 2) (hy : orderOf y.val = 2) :
      IsConj x.val y.val ↔ IsConj (D.leftToCarrier x) (D.rightToCarrier y) := by
    have hxE : orderOf (D.leftToCarrier x) = 2 :=
      (orderOf_injective _ D.leftToCarrier_injective x).trans
        ((Subgroup.orderOf_coe x).symm.trans hx)
    have hyE : orderOf (D.rightToCarrier y) = 2 :=
      (orderOf_injective _ D.rightToCarrier_injective y).trans
        ((Subgroup.orderOf_coe y).symm.trans hy)
    have hf := d.ree_endpoint_involution_fusion_iff h hp m hH he D
      (i := false) (j := true)
      ⟨D.leftToCarrier x,(D.full.left x).property⟩
      ⟨D.rightToCarrier y,(D.full.right y).property⟩ hxE hyE
    rw [D.endpointInverse_left,D.endpointInverse_right] at hf
    exact hf
  obtain ⟨t,v,ht,_,_,_,_,hmark,hmap,_,_,_,_,hC,_,_⟩ :=
    d.ree_short_ambient_comparison h hH hp m he D
      (ReeF4.SourceCompletion.involution_root_classes m hm)
      (fun x y hx hy hxy =>
        (d.ree_left_involution_fusion_iff h hp m hH he D x y hx hy).mp hxy)
      hcross
  have hrec := d.ree_ambient_recognition_of_short_centralizer h hH hp m he D t v ht hmark hmap hC
  exact ⟨hn,hm,hrec.2.2.2.2⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
