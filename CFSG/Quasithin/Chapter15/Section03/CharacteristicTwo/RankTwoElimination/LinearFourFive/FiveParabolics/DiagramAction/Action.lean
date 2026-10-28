module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.ParabolicConstruction
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.Geometry

/-!
# The marked component action and its actual subgroup images

Conjugation by N(L) descends through the characteristic two-core and is
transported by the specified projective marking to GL₅(2). The formulas
on representatives are retained. Restriction to X ≤ L has two-group
kernel and hence identifies the intrinsic two-core quotients of X and
its image. These constructions supply the maps used in the diagram
argument; they do not assume innerness.

Source: Aschbacher–Smith, 15.3.24, printed p.1129 of refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.DiagramAction
variable {G : Type*} [Group G] {L : Subgroup G}

noncomputable def modelNormalizerAction (e : (L ⧸ pCore 2 L) ≃* Projective 5) :
    normalizer (L : Set G) →* MulAut (LinearGroup 5) :=
  (MulAut.congr (e.trans (projectiveEquivLinear (by decide)))).toMonoidHom.comp
    ((quotientAut (pCore 2 L)).comp L.normalizerMonoidHom)

theorem modelNormalizerAction_apply (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (s : normalizer (L : Set G)) (l : L) :
    modelNormalizerAction e s (linearAction (by decide) e l) =
      linearAction (by decide) e (L.normalizerMonoidHom s l) := by
  let f := e.trans (projectiveEquivLinear (by decide))
  change f ((quotientAut (pCore 2 L) (L.normalizerMonoidHom s))
    (f.symm (f (QuotientGroup.mk' (pCore 2 L) l)))) = _
  rw [f.symm_apply_apply, quotientAut_apply_mk]
  rfl

noncomputable def subgroupImageMap (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    {X : Subgroup G} (hXL : X ≤ L) :
    X →* (X.subgroupOf L).map (linearAction (by decide) e) :=
  ((linearAction (by decide) e).subgroupMap (X.subgroupOf L)).comp
    (subgroupOfEquivOfLe hXL).symm.toMonoidHom

theorem subgroupImageMap_apply (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    {X : Subgroup G} (hXL : X ≤ L) (x : X) :
    (subgroupImageMap e hXL x : LinearGroup 5) =
      linearAction (by decide) e (inclusion hXL x) := rfl

theorem subgroupImageMap_surjective (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    {X : Subgroup G} (hXL : X ≤ L) : Function.Surjective (subgroupImageMap e hXL) :=
  ((linearAction (by decide) e).subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hXL).symm.surjective

theorem subgroupImageMap_ker_isPGroup (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    {X : Subgroup G} (hXL : X ≤ L) : IsPGroup 2 (subgroupImageMap e hXL).ker := by
  have he : (subgroupImageMap e hXL).ker = (pCore 2 L).comap (inclusion hXL) := by
    ext x
    change subgroupImageMap e hXL x = 1 ↔ _
    rw [Subtype.ext_iff]
    change linearAction (by decide) e (inclusion hXL x) = 1 ↔ _
    rw [← MonoidHom.mem_ker, linearAction_ker]
    rfl
  rw [he]
  exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hXL)

theorem modelNormalizerAction_subgroupImage (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    {X : Subgroup G} (hXL : X ≤ L) (s : G)
    (hsL : s ∈ normalizer (L : Set G)) (hsX : s ∈ normalizer (X : Set G)) (x : X) :
    modelNormalizerAction e ⟨s, hsL⟩ (subgroupImageMap e hXL x : LinearGroup 5) =
      (subgroupImageMap e hXL (X.normalizerMonoidHom ⟨s, hsX⟩ x) : LinearGroup 5) := by
  rw [subgroupImageMap_apply, modelNormalizerAction_apply, subgroupImageMap_apply]
  rfl

variable [Finite G]

noncomputable def subgroupImageCoreEquiv (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    {X : Subgroup G} (hXL : X ≤ L) :
    (X ⧸ pCore 2 X) ≃*
      ((X.subgroupOf L).map (linearAction (by decide) e) ⧸
        pCore 2 ((X.subgroupOf L).map (linearAction (by decide) e))) := by
  letI : Finite ((X.subgroupOf L).map (linearAction (by decide) e)) :=
    Finite.of_surjective _ (subgroupImageMap_surjective e hXL)
  exact MonoidHom.quotientPCoreEquivOfSurjective (subgroupImageMap e hXL)
    (subgroupImageMap_surjective e hXL) (subgroupImageMap_ker_isPGroup e hXL)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.DiagramAction
end
