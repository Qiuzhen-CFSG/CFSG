module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalSections.NoFF
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.Representation.BinaryOffender.AmbientSectionTransport

/-!
# The literal moved central section in the ambient group

For K ≤ J ≤ D with K normal in D, the moved space computed in J equals
[V,K]. Normality makes this space and its K-fixed subspace D-invariant.
The ambient construction retains the original submodule carriers, so the
quotient actions agree on J without changing coordinates. Consequently a
repeated-natural identification over J transports to D with the same
multiplicity and one common marking of K. No summand invariance is used.

Source: Aschbacher–Smith, B.5.1, printed pp.99–103, applied in F.9.18(7)
and 13.8.20, printed p.955 (combined manuscript of 1 March 2004).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Representation.SL3FourNaturalDual
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NoFF.Recognition
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {K J : Subgroup D} (hKJ : K ≤ J)

include hKJ in
/-- Restriction to an overgroup preserves the actual commutator subspace. -/
lemma moved_subgroupOf : moved (ρ.comp J.subtype) (K.subgroupOf J) = moved ρ K := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, v, hv, rfl⟩
    exact Submodule.subset_span ⟨k, hk, v, hv, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, v, hv, rfl⟩
    exact Submodule.subset_span ⟨⟨k, hKJ hk⟩, hk, v, hv, rfl⟩

variable [K.Normal]

/-- The same moved subspace, with its ambient invariant action. -/
def ambientSpace (s : MovedSection (ρ.comp J.subtype) (K.subgroupOf J)) :
    Subrepresentation ρ where
  toSubmodule := s.space.toSubmodule
  apply_mem_toSubmodule g v hv := by
    have he : s.space.toSubmodule = moved ρ K := s.space_eq.trans (moved_subgroupOf ρ hKJ)
    rw [he] at hv ⊢
    apply (subspaceCommutator_invariant_normalizer ρ (A := ⊤)
      (D := ⊤) (X := K) ?_ ?_ (mem_top g) v).2 hv
    · apply le_subspaceStabilizer
      intros
      trivial
    · rw [Subgroup.normalizer_eq_top]

/-- The same fixed subspace, invariant under the ambient group. -/
def ambientCentral (s : MovedSection (ρ.comp J.subtype) (K.subgroupOf J)) :
    Subrepresentation (ambientSpace ρ hKJ s).toRepresentation where
  toSubmodule := s.central.toSubmodule
  apply_mem_toSubmodule g v hv := by
    have he : s.central.toSubmodule = fixedSpace (ambientSpace ρ hKJ s).toRepresentation K := by
      rw [s.central_eq]
      exact fixedSpace_subgroupOf (ambientSpace ρ hKJ s).toRepresentation K J hKJ
    rw [he] at hv ⊢
    exact (fixedSpace_stable_of_normal _ K (mem_top g) v).2 hv

/-- Extend the actual moved central section to the ambient group. -/
def ambientSection (s : MovedSection (ρ.comp J.subtype) (K.subgroupOf J)) :
    MovedSection ρ K where
  space := ambientSpace ρ hKJ s
  space_eq := s.space_eq.trans (moved_subgroupOf ρ hKJ)
  central := ambientCentral ρ hKJ s
  central_eq := by
    change s.central.toSubmodule = _
    rw [s.central_eq]
    exact fixedSpace_subgroupOf (ambientSpace ρ hKJ s).toRepresentation K J hKJ

/-- The extended quotient action agrees with the original action on J. -/
lemma ambientSection_action (s : MovedSection (ρ.comp J.subtype) (K.subgroupOf J))
    (j : J) (w : s.space.toSubmodule ⧸ s.central.toSubmodule) :
    (ambientSection ρ hKJ s).action ρ (j : D) w = s.action (ρ.comp J.subtype) j w := by
  induction w using Submodule.Quotient.induction_on with | _ w => rfl

/-- Transport natural coordinates to D, retaining the common marking and multiplicity. -/
noncomputable def ambientRepeatedNaturalSection
    (s : RepeatedNaturalSection (ρ.comp J.subtype) (K.subgroupOf J)) :
    RepeatedNaturalSection ρ K where
  sectionData := ambientSection ρ hKJ s.sectionData
  marking := (subgroupOfEquivOfLe hKJ).symm.trans s.marking
  copies := s.copies
  positive := s.positive
  coordinates := s.coordinates
  natural_action g w i := by
    rw [ambientSection_action ρ hKJ s.sectionData ⟨g, hKJ g.property⟩ w]
    exact s.natural_action ((subgroupOfEquivOfLe hKJ).symm g) w i

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NoFF.Recognition
