module
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.UnmarkedQuadratic.Mathieu.M12.Actors
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.UnmarkedQuadratic.Mathieu.M12.Certificates
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.UnmarkedQuadratic.Mathieu.NativeBounds
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.Remaining

/-!
# The unmarked M12 quadratic source exclusion

The actual full-automorphism heart estimate is assembled from checked Sylow
certificates. Existing cubic source recognition removes central covers and
embeds the entire original actor equivariantly in this native action. Thus
the original source, and its literal B.4 consumer, have quadratic ratio above
two without an FF, module-marking, or local-action hypothesis.

Source: Aschbacher--Smith B.4.5 and K.4.4, printed pp.87,459--460.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu M12ExceptionalExtension
open CFSG.Quasithin.ChapterH.Section10To12
open CFSG.Quasithin.ChapterH.Section10To12.M12Calculations
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.Mathieu

private theorem native_strict (hp : ∀ i, M12.prefixCheck i) (hm : ∀ i, M12.matrixCheck i)
    (hs : ∀ i, M12.squareCheck i) (hr : ∀ v w, M12.rejectionCheck v w)
    (hn : ∀ v, M12.neighborsCheck v) (hc : ∀ v, M12.rankCheck v) :
    2 < quadraticRatio Ambient.automorphismRepresentation := by
  have he (g : MulAut Sporadic.Mathieu.M12) (v : M12Heart) :
      heartEquiv.symm (Ambient.automorphismRepresentation g v) =
        M12.coordinateRepresentation (automorphismEquiv.symm g) (heartEquiv.symm v) := by
    apply heartEquiv.injective
    rw [LinearEquiv.apply_symm_apply, M12.coordinate_equivariant,
      MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact (M12.strict_of_certificates hp hm hs hr hn hc).trans_le
    (quadraticRatio_le_of_injective_equivariant Ambient.automorphismRepresentation
      M12.coordinateRepresentation automorphismEquiv.symm.toMonoidHom
      automorphismEquiv.symm.injective heartEquiv.symm he)

universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

private theorem source_strict
    (hn : 2 < quadraticRatio Ambient.automorphismRepresentation)
    (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m12.Carrier)) :
    2 < quadraticRatio ρ := by
  rcases h.fitting with rfl
  obtain ⟨e⟩ := he
  have hs : ComponentRecognition.KnownFFTypes.Sporadic.M12Source.Hypotheses ρ := {
    sqtk := h.sqtk, quasisimple := h.quasisimple, faithful := h.faithful,
    irreducible := h.irreducible, cubic_ratio := h.smallCubic }
  obtain ⟨_,f,_,hf,_,_,⟨E⟩⟩ :=
    ComponentRecognition.KnownFFTypes.Sporadic.M12Source.source_native_ambient_equiv ρ hs e
  exact hn.trans_le (quadraticRatio_le_of_injective_equivariant ρ _ f hf E.toLinearEquiv
    (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v))

/-- The actual full automorphism action on the native M12 heart has strict
quadratic ratio. All finite Sylow calculations are kernel checked. -/
theorem automorphism_quadraticRatio_gt_two :
    2 < quadraticRatio Ambient.automorphismRepresentation :=
  native_strict M12.prefix_check M12.matrix_check M12.square_check M12.reject_check
    M12.neighbors_check M12.rank_check

/-- Native source recognition preserves central covers and all ambient outer
actors when transferring the strict heart estimate. -/
theorem m12_quadraticRatio_gt_two (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m12.Carrier)) :
    2 < quadraticRatio ρ := source_strict automorphism_quadraticRatio_gt_two h he

/-- Exclude the actual M12 central quotient from the small-quadratic source. -/
theorem no_m12 (h : ChapterK.RankOne.SourceHypotheses ρ L) (hq : quadraticRatio ρ ≤ 2)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m12.Carrier)) : False :=
  (not_lt_of_ge hq) (m12_quadraticRatio_gt_two h he)

open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases in
/-- Exclude the M12 constructor at the original B.4 consumer. -/
theorem b4_no_m12 [Finite V] (h : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    (hq : quadraticRatio ρ ≤ 2)
    (he : Nonempty (generalizedFitting G ⧸ center (generalizedFitting G) ≃*
      KnownSimple.SporadicName.m12.Carrier)) : False :=
  no_m12 ⟨h.sqtk, rfl, h.quasisimple, h.faithful, h.irreducible,
    (Representation.BinaryOffender.cubicRatio_le_quadraticRatio ρ).trans hq⟩ hq he

end CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.Mathieu
