module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.CompleteSource
public import CFSG.Quasithin.Chapter3.Section01.BaumannSylow.SpanApplication
/-!
# Original 3.1.7 reduction to the actual paired symmetric-five action

The original qrc configuration supplies the reduced Sylow omega-center orbit
in H. The complete known-simple classification and the single-factor/linear
Baumann arguments apply to that literal action. Both the direct Sylow case
and the single symmetric-five extension give O₂(M₀) Sylow in O²(H)O₂(M₀)
by the genuine Baumann span theorem. Only the same marked symmetric-five
pair remains for its componentwise C.1.24 argument.

Source: Aschbacher--Smith 3.1.7 and E.2.3, pp.575--576 and216--217.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- No earlier classification, module-coordinate or single-factor Sylow premise remains. -/
theorem QrcHypotheses.residual_sylow_or_paired_five
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    let S := T.subtype h.right_mem.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let hU := h.sylowOmega_reduced (hG.evenCharacteristic T)
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set H)
    Chapter1.IsSylowIn 2 (M₀.pCoreIn 2)
      ((pResidual 2 H).map H.subtype ⊔ M₀.pCoreIn 2) ∨
      ChapterE.ThompsonAction.SymmetricFivePairSource S U (QuotientGroup.mk' C)
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) := by
  obtain ⟨hsq,_,hp,hU,hj⟩ := h.e23_hypotheses hG hM hu hJ hZ
  rcases ChapterE.ThompsonAction.source_sylow_or_paired_five hsq _ hp _ hU hj with hs | hpair
  · rcases hs with hs | ⟨S₁,hs,hbs,_,hspan⟩
    · exact Or.inl (h.residual_sylow_of_baumann_sylow hJ hs)
    · exact Or.inl (h.residual_sylow_of_baumann_span hJ hp S₁ hs hbs hspan)
  · exact Or.inr hpair
end CFSG.Quasithin.Chapter3
