module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Residual
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.CentralKernelElementCentralizer

/-!
# The full residual seed in a Hermitian ordinary J₄ cover

The element-centralizer map under a central two-kernel has normal image
with two-group cokernel. Its image therefore contains the native perfect
residual. Restriction to that image preserves the residual, and the
solvable-kernel correspondence lifts both its C-component property and
its actual M₂₂ radical quotient. The full central kernel is retained;
surjectivity onto the native element centralizer is not required.

The original chosen-module application is in
NonFFSourceNonMathieuHermitianFieldFourResidualSeed. This supplies the
full seed needed for the ambient component comparison in 4.4.3, as used
in 8.2.7. Source: Aschbacher--Smith, printed pp.623,718,
refs/quasithin.pdf; native carrier facts retain their imported attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open Janko4.InvolutionCentralizers
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem lift_seed {C Q : Type*} [Group C] [Finite C] [Group Q] [Finite Q]
    (f : C →* Q) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (hQ : (solvableResidual Q).IsCComponent)
    (eQ : (solvableResidual Q ⧸ solvableRadical (solvableResidual Q)) ≃* Sporadic.Mathieu.M22) :
    (solvableResidual C).IsCComponent ∧
      Nonempty ((solvableResidual C ⧸ solvableRadical (solvableResidual C)) ≃* Sporadic.Mathieu.M22) := by
  have hc := residual_isCComponent_of_surjective f hf hQ
  let e := MulEquiv.subgroupCongr (map_solvableResidual_eq f hf)
  let g : solvableResidual C →* solvableResidual Q :=
    e.toMonoidHom.comp (f.subgroupMap (solvableResidual C))
  have hg : Function.Surjective g := e.surjective.comp (f.subgroupMap_surjective _)
  let : Group.IsSolvable g.ker := by
    change Group.IsSolvable (e.toMonoidHom.comp (f.subgroupMap (solvableResidual C))).ker
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (solvableResidual C).subtype.subgroupComap f.ker)
      (fun x y h => Subtype.ext (Subtype.ext
        (congrArg (fun z : f.ker => (z : C)) h)))
  exact ⟨hc,⟨(solvableRadicalQuotientEquiv g hg).trans eQ⟩⟩

/-- The entire element-centralizer residual survives a central two-cover,
even when its map to the native centralizer is not surjective. -/
theorem janko_two_cover_involution_residual
    {K : Type*} [Group K] [Finite K]
    (f : K →* Janko4.Model) (hf : Function.Surjective f)
    (hk : f.ker ≤ center K) (hp : IsPGroup 2 f.ker)
    (z : K) (hz : orderOf (f z) = 2) :
    (solvableResidual (centralizer ({z} : Set K))).IsCComponent ∧
      Nonempty ((solvableResidual (centralizer ({z} : Set K)) ⧸
        solvableRadical (solvableResidual (centralizer ({z} : Set K)))) ≃*
          Sporadic.Mathieu.M22) := by
  let C := centralizer ({f z} : Set Janko4.Model)
  let c := f.elementCentralizerMap z
  obtain ⟨hn,hq⟩ := f.elementCentralizerMap_normal_pGroup_cokernel hf hk hp z
  let := hn
  let := hq.isNilpotent
  have hr : solvableResidual C ≤ c.range := solvableResidual_le_of_solvable_quotient _
  have hnative : (solvableResidual C).IsCComponent ∧
      Nonempty ((solvableResidual C ⧸ solvableRadical (solvableResidual C)) ≃*
        Sporadic.Mathieu.M22) := by
    rcases centralizer_equiv_first_or_second (f z) hz with hfirst | hsecond
    · obtain ⟨e⟩ := hfirst
      let : Group.IsSolvable e.toMonoidHom.ker := by
        rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
        infer_instance
      exact lift_seed e.toMonoidHom e.surjective first_residual_component.1
        first_residual_component.2.some
    · obtain ⟨e⟩ := hsecond
      let : Group.IsSolvable e.toMonoidHom.ker := by
        rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
        infer_instance
      exact lift_seed e.toMonoidHom e.surjective second_residual_component.1
        second_residual_component.2.some
  have he : solvableResidual c.range = (solvableResidual C).subgroupOf c.range := by
    apply map_injective c.range.subtype_injective
    rw [map_solvableResidual_eq_of_residual_le c.range hr,map_subgroupOf_eq_of_le hr]
  have hcomponent : (solvableResidual c.range).IsCComponent := by
    rw [he]
    exact hnative.1.subgroupOf hr
  let e := solvableResidualEquivOfSolvableQuotient c.range
  let q := (QuotientGroup.congr _ _ e (map_solvableRadical_equiv e)).trans hnative.2.some
  let : Group.IsSolvable c.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    have hc : IsPGroup 2 c.ker := by
      rw [f.elementCentralizerMap_ker z]
      exact hp.comap_subtype
    let := hc.isNilpotent
    infer_instance
  exact lift_seed c.rangeRestrict c.rangeRestrict_surjective hcomponent q

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
