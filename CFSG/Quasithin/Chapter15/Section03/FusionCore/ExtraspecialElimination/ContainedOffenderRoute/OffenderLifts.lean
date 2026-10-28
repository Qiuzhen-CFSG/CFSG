module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationPreparation
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Best offenders contained in the actual endpoint

B.1.4(4) supplies a best subgroup of an ordinary offender. Lift this subgroup
inside the specified elementary endpoint, rather than through the whole
local group. Its star image is exactly the selected subgroup. Conjugation
then gives a compatible lift inside the other endpoint on the same literal
SectionAction. Quadraticity descends from the endpoint; no best property of
the whole endpoint is asserted.

The strong version will be used again after the component reduction; its
newly chosen subgroup need not belong to the first offender-generated actor.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.4(4),
printed pp.68–69, and proof of 15.3.49(h), (n), printed pp.1143–1145.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute

open Subgroup Representation.BinaryOffender ComponentReduction
open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- The preimage restricted to the actual endpoint before mapping into `G`. -/
def endpointLift (H E : Subgroup G) (B : Subgroup (H ⧸ pCore 2 H)) : Subgroup G :=
  (E.subgroupOf H ⊓ B.comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype

theorem endpointLift_le (H E : Subgroup G) (B : Subgroup (H ⧸ pCore 2 H)) :
    endpointLift H E B ≤ E := by
  rintro x ⟨a, ha, rfl⟩
  exact ha.1

theorem endpointLift_le_local (H E : Subgroup G) (B : Subgroup (H ⧸ pCore 2 H)) :
    endpointLift H E B ≤ H := map_subtype_le _

/-- There is no enlargement of the chosen star subgroup in taking its lift. -/
theorem starImage_endpointLift (H E : Subgroup G) (B : Subgroup (H ⧸ pCore 2 H))
    (hBE : B ≤ starImage H E) : starImage H (endpointLift H E B) = B := by
  unfold starImage endpointLift Subgroup.subgroupOf
  rw [comap_map_eq_self_of_injective H.subtype_injective]
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha.2
  · intro hx
    obtain ⟨a, ha, he⟩ := hBE hx
    refine ⟨a, ⟨ha, ?_⟩, he⟩
    change QuotientGroup.mk' (pCore 2 H) a ∈ B
    rwa [he]

theorem endpointLift_elementary (H E : Subgroup G) [IsElementaryAbelian 2 E]
    (B : Subgroup (H ⧸ pCore 2 H)) : IsElementaryAbelian 2 (endpointLift H E B) :=
  IsElementaryAbelian.of_le (endpointLift_le H E B)

/-- The two independently selected objects are kept separate: an elementary
ambient lift and its genuine best-offender star image. -/
structure ContainedBest (H U Z E : Subgroup G) [IsElementaryAbelian 2 U]
    (action : SectionAction H U Z) where
  carrier : Subgroup G
  le_endpoint : carrier ≤ E
  le_local : carrier ≤ H
  elementary : IsElementaryAbelian 2 carrier
  best : IsBestOffender action.representation (starImage H carrier)
  quadratic : IsQuadratic action.representation (starImage H carrier)

/-- Construct a contained best offender without a corank hypothesis. -/
theorem exists_containedBest [Finite G]
    (H U Z E : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 E]
    (action : SectionAction H U Z)
    (hoff : IsOffender action.representation (starImage H E))
    (hquad : IsQuadratic action.representation (starImage H E)) :
    Nonempty (ContainedBest H U Z E action) := by
  obtain ⟨B, hBE, hbest⟩ := hoff.exists_bestOffender action.representation
  refine ⟨⟨endpointLift H E B, endpointLift_le H E B,
    endpointLift_le_local H E B, endpointLift_elementary H E B, ?_, ?_⟩⟩
  · rwa [starImage_endpointLift H E B hBE]
  · rw [starImage_endpointLift H E B hBE]
    exact fun a ha b hb v => hquad a (hBE ha) b (hBE hb) v

/-- Strong offending yields a contained strong best offender, again on the
same module and inside the same specified elementary endpoint. -/
theorem exists_strong_containedBest [Finite G]
    (H U Z E : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 E]
    (action : SectionAction H U Z)
    (hoff : IsStrongOffender action.representation (starImage H E))
    (hquad : IsQuadratic action.representation (starImage H E)) :
    ∃ d : ContainedBest H U Z E action,
      IsStrongOffender action.representation (starImage H d.carrier) := by
  obtain ⟨B, hBE, hbest, hstrong⟩ := hoff.exists_bestOffender action.representation
  have hq : IsQuadratic action.representation (starImage H (endpointLift H E B)) := by
    rw [starImage_endpointLift H E B hBE]
    exact fun a ha b hb v => hquad a (hBE ha) b (hBE hb) v
  refine ⟨⟨endpointLift H E B, endpointLift_le H E B,
    endpointLift_le_local H E B, endpointLift_elementary H E B,
    (starImage_endpointLift H E B hBE).symm ▸ hbest, hq⟩, ?_⟩
  change IsStrongOffender action.representation (starImage H (endpointLift H E B))
  rwa [starImage_endpointLift H E B hBE]

namespace ContainedBest

variable {H U Z E : Subgroup G} [IsElementaryAbelian 2 U]
    {action : SectionAction H U Z} (d : ContainedBest H U Z E action)

/-- Conjugate the actual lift and endpoint simultaneously. -/
noncomputable def conjugate (h : H) :
    ContainedBest H U Z (E.map (MulAut.conj (h : G)).toMonoidHom) action := by
  let := d.elementary
  have hpair := quadratic_bestOffender_conjugate H U Z d.carrier
    action d.le_local h d.best d.quadratic
  exact ⟨d.carrier.map (MulAut.conj (h : G)).toMonoidHom,
    map_mono d.le_endpoint,
    FactorGeneration.selectedConjugate_le H d.carrier d.le_local h,
    IsElementaryAbelian.map _, hpair.1, hpair.2⟩

theorem conjugate_starImage (h : H) :
    starImage H (d.conjugate h).carrier =
      (starImage H d.carrier).map
        (MulAut.conj (QuotientGroup.mk' (pCore 2 H) h)).toMonoidHom :=
  starImage_map_conj H d.carrier d.le_local h

theorem conjugate_span (h : H) :
    localSpan (d.conjugate h).carrier H = localSpan d.carrier H :=
  FactorGeneration.selectedConjugate_span H d.carrier h

/-- Strength is retained under the same conjugation used for the endpoint. -/
theorem conjugate_strong [Finite G] (h : H)
    (hs : IsStrongOffender action.representation (starImage H d.carrier)) :
    IsStrongOffender action.representation (starImage H (d.conjugate h).carrier) := by
  refine ⟨(d.conjugate h).best.1, ?_⟩
  apply (fixedCodim_lt_rank_iff action.representation _).mpr
  rw [d.conjugate_starImage, weight_map_conj]
  exact (fixedCodim_lt_rank_iff action.representation _).mp hs.2

/-- Placement of the endpoint in a parabolic two-core passes to this lift's
image; the endpoint itself is never substituted for the contained offender. -/
theorem starImage_le {P : Subgroup (H ⧸ pCore 2 H)} (hEP : starImage H E ≤ P) :
    starImage H d.carrier ≤ P :=
  (map_mono (comap_mono d.le_endpoint)).trans hEP

end ContainedBest
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute
