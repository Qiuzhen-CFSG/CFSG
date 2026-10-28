module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.Criteria
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.ModelOffenders.Normalizers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.ModelOffenders.ExplicitOffenders
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# No ambient FF-offenders on the explicit cover models

An intertwining equivalence conjugates a faithful ambient action into the
linear automorphism group of its restricted model. Normality of the image of
SL₃(2) puts this conjugated action inside the model's full linear normalizer.
Every elementary offender then maps injectively to an offender with the same
rank and fixed codimension. Thus normalizer coverage and offender exclusion
for an explicit actor group suffice to prove the original overgroup claim.

The full normalizer calculations and explicit actor exclusions discharge both
premises for the mixed and doubled models. Thus `CoverModels.mixed_noFF` and
`CoverModels.doubled_noFF` exclude offenders in every faithful finite overgroup
whose restricted matrix-group action is equivalent to the indicated model.
Source context: Aschbacher–Smith, combined manuscript (1 March 2004),
C.1.34(2),(5), printed pp.136–137, and I.1.5–6, printed p.408.
This is an independent proposed route, not a quoted MS93 lemma.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders
open Representation Representation.BinaryOffender
open LinearMap.GeneralLinearGroup

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

/-- Transport an ambient faithful overgroup and each of its offenders into a
concrete linear group containing the full normalizer of the restricted model.
Normality is needed only for the matrix-group image in the given overgroup. -/
theorem noFFOvergroups_of_normalizer_le.{u, v}
    (τ : Representation (ZMod 2) MatrixGroup M) (K : Subgroup (BinaryGL M))
    (hK : normalizer τ ≤ K) (hFF : ¬ IsFFModule (subgroupAction K)) :
    NoFFOvergroups.{u, v} τ := by
  intro W _ _ _ H _ _ δ ι hδ hι he hδFF
  obtain ⟨e⟩ := he
  let f : H →* BinaryGL M := (generalLinearEquiv (ZMod 2) M).toMonoidHom.comp
    ((congrLinearEquiv e.toLinearEquiv).toMonoidHom.comp δ.asGroupHom)
  have hf (g : H) (w : W) : f g (e w) = e (δ g w) := by
    change e (δ g (e.symm (e w))) = _
    rw [e.symm_apply_apply]
  have hinj : Function.Injective f := by
    intro g h hgh
    apply hδ
    apply LinearMap.ext
    intro w
    apply e.injective
    change e (δ g w) = e (δ h w)
    rw [← hf, ← hf, hgh]
  have hcomp : f.comp ι = linearAction τ := by
    ext g m
    change e (δ (ι g) (e.symm m)) = τ g m
    have heq := LinearMap.congr_fun (e.isIntertwining' g) (e.symm m)
    change e (δ (ι g) (e.symm m)) = τ g (e (e.symm m)) at heq
    simpa only [e.apply_symm_apply] using heq
  have hrange : ι.range.map f = (linearAction τ).range := by
    rw [← MonoidHom.range_comp, hcomp]
  have hmem (g : H) : f g ∈ normalizer τ := by
    change f g ∈ Subgroup.normalizer (linearAction τ).range
    rw [← hrange]
    apply Subgroup.le_normalizer_map f
    apply Subgroup.mem_map_of_mem
    let : ι.range.Normal := hι
    rw [Subgroup.normalizer_eq_top]
    trivial
  let F : H →* K := f.codRestrict K (fun g => hK (hmem g))
  have hF : Function.Injective F := by
    intro g h heq
    exact hinj (congrArg Subtype.val heq)
  exact hFF (hδFF.map_equivariant δ (subgroupAction K) F hF e.toLinearEquiv
    (fun g w => (hf g w).symm))

/-- The mixed overgroup exclusion follows from normalizer coverage and offender
exclusion for the explicit generated group. -/
theorem mixed_noFF_of_actor_results.{u,v}
    (hN : normalizer mixed ≤ mixedActors)
    (hF : ¬ IsFFModule (subgroupAction mixedActors)) :
    NoFFOvergroups.{u,v} mixed :=
  noFFOvergroups_of_normalizer_le mixed mixedActors hN hF

/-- The doubled overgroup exclusion follows from normalizer coverage and offender
exclusion for the explicit generated group. -/
theorem doubled_noFF_of_actor_results.{u,v}
    (hN : normalizer doubled ≤ doubledActors)
    (hF : ¬ IsFFModule (subgroupAction doubledActors)) :
    NoFFOvergroups.{u,v} doubled :=
  noFFOvergroups_of_normalizer_le doubled doubledActors hN hF

end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders

namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels

/-- Every faithful finite overgroup with normal matrix-group image acting as
the mixed universal cover admits no nontrivial elementary abelian offender. -/
theorem mixed_noFF.{u, v} : NoFFOvergroups.{u, v} mixed :=
  ModelOffenders.mixed_noFF_of_actor_results
    ModelOffenders.mixed_normalizer_le_actors
    ModelOffenders.mixedActors_not_isFFModule

/-- Every faithful finite overgroup with normal matrix-group image acting as
the doubled universal cover admits no nontrivial elementary abelian offender. -/
theorem doubled_noFF.{u, v} : NoFFOvergroups.{u, v} doubled :=
  ModelOffenders.doubled_noFF_of_actor_results
    ModelOffenders.doubled_normalizer_le_actors
    ModelOffenders.doubledActors_not_isFFModule

end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels
