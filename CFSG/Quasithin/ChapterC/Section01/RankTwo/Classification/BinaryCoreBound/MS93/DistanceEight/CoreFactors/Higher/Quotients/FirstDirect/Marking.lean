module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.FirstDirect.Coordinates

/-!
# First-hat coordinates with the literal source projection

The natural-section actor and the original projection have exactly the
same kernel after the actual stabilizer embedding. Their quotient
isomorphisms therefore give a uniquely compatible marking. The coordinate
conjugation equation is transported through that marking without changing
the original quotient or its kernel.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(v), pp.898--899.
The following orientation leaf compares this marking with the actual
natural subgroup, rather than choosing an unrelated abstract model.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.FirstDirect
open PathCentrality
open Early.Orbit.Source.HatIdentity.Third
open Escape.Propagation.Backward.Products.Selection.Choices
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
theorem base_color (R : Subgroup M) : color R (alpha R) = false := rfl

/-- The original embedding, viewed as an isomorphism onto its stabilizer. -/
noncomputable def baseEquiv (R : Subgroup M) : M ≃* stabilizer R (alpha R) :=
  (MonoidHom.ofInjective (embedM_injective R)).trans
    (MulEquiv.subgroupCongr (stabilizer_m_base R).symm)

omit [Finite M] in
theorem baseEquiv_coe (m : M) : (baseEquiv R m : FreeAmalgam R) = embedM R m := rfl

/-- The marked natural-quotient actor pulled through the original embedding. -/
noncomputable def quotientActor (common : CommonFacts R source geometry)
    (s : Escape.NaturalSectionAt (alpha R) (V R (alpha R)) (Z R (alpha R))) : M →* SL :=
  (SourceLines.actor common (base_color R) s).comp (baseEquiv R).toMonoidHom

theorem quotientActor_surjective (common : CommonFacts R source geometry)
    (s : Escape.NaturalSectionAt (alpha R) (V R (alpha R)) (Z R (alpha R))) :
    Function.Surjective (quotientActor common s) :=
  (SourceLines.actor_surjective common (base_color R) s).comp (baseEquiv R).surjective

theorem quotientActor_kernel (common : CommonFacts R source geometry)
    (s : Escape.NaturalSectionAt (alpha R) (V R (alpha R)) (Z R (alpha R))) :
    (quotientActor common s).ker = source.projection.ker := by
  ext m
  change baseEquiv R m ∈ (SourceLines.actor common (base_color R) s).ker ↔ _
  rw [SourceLines.actor_kernel common (base_color R) s, source.projection_kernel]
  change embedM R m ∈ Q R (alpha R) ↔ m ∈ pCore 2 M
  rw [Q_alpha R source.two_group source.core_le, mem_map_iff_mem (embedM_injective R)]

/-- The quotient marking forced by equality of the two literal kernels. -/
noncomputable def sourceMarking (common : CommonFacts R source geometry)
    (s : Escape.NaturalSectionAt (alpha R) (V R (alpha R)) (Z R (alpha R))) : SL ≃* SL :=
  (QuotientGroup.quotientKerEquivOfSurjective source.projection source.projection_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (quotientActor_kernel common s).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (quotientActor common s) (quotientActor_surjective common s)))

theorem sourceMarking_apply (common : CommonFacts R source geometry)
    (s : Escape.NaturalSectionAt (alpha R) (V R (alpha R)) (Z R (alpha R))) (m : M) :
    sourceMarking common s (source.projection m) = quotientActor common s m := by
  let e := QuotientGroup.quotientKerEquivOfSurjective source.projection source.projection_surjective
  have he : e (QuotientGroup.mk m) = source.projection m := rfl
  change (QuotientGroup.quotientKerEquivOfSurjective (quotientActor common s) (quotientActor_surjective common s))
    ((QuotientGroup.quotientMulEquivOfEq (quotientActor_kernel common s).symm) (e.symm (source.projection m))) = _
  rw [← he,e.symm_apply_apply]
  rfl

/-- Equivariance in the literal source projection; only the coordinate
marking remains to be identified as dual to CommonFacts.natural. -/
theorem coordinates_source_action (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : Escape.NaturalSectionAt (alpha R) (V R (alpha R)) (Z R (alpha R)))
    (m : M) (x y : hatV R (alpha R) (p.walk.getVert 6))
    (hy : (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹) :
    (coordinates common earlier p s y).toAdd =
      (sourceMarking common s (source.projection m)).val.mulVec
        (coordinates common earlier p s x).toAdd := by
  rw [sourceMarking_apply]
  exact (SourceLines.lineFactor common (base_color R) s).action (baseEquiv R m) (mem_top _) _ _
    (Subtype.ext hy)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.FirstDirect
