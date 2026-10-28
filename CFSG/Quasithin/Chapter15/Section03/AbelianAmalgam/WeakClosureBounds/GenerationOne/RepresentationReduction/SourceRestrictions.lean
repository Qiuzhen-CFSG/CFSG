module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.Setup
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FaithfulSections
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.ModuleIdentifications

/-!
# Source restrictions: faithful sections and the local quotient

The ratio bound supplies a quadratic elementary actor on the literal U/Z,
with U the conjugate span of ZS and actor H/O₂(H). Given faithfulness of this
actor on the orbit of components, the component-normal-subgroup dichotomy
and fixed-codimension inequality prove the F.9.18(6) section alternative on
faithful action images. The images retain their actual representations.

Oddness of the defining-field exponent rules out equality with the field
order in the even-exponent orthogonal SL₂ alternative. This arithmetic step
must be applied after identifying the same defining field in both source
clauses. It does not classify arbitrary isomorphic group models.

The imported identity interfaces keep invariant central quotients, actual
induced diagram automorphisms and nonsplit central extensions. Their model
witnesses are not asserted here. The remaining assembly obligations are:
* the full F.9.18(4),(5) and B.4.2/B.4.5 restrictions, yielding cases (i)--(iii);
* the B.4.2/B.5.1 finite faithful FF exclusions and SL₂ extension alternative;
* matching those outputs with the actual component, Borel and section images.
No theorem here establishes the full representation restriction or 15.3.65.

The local section theorem additionally needs the actual component-image
property, its residual-orbit identity, and a bounded quadratic actor faithful
on that orbit (the content of F.9.18(2),(3)). These are not consequences of
the scalar ratio bound alone. All such premises remain for source assembly.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.65,
printed p.1152; F.9.18, pp.325--326; B.4.2/B.4.5, pp.86--87; B.5.1, pp.99--100.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

section Local
variable {G : Type*} [Group G] [Finite G] {H Z ZS : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]

/-- Extract the bounded quadratic actor on the literal source module:
H/O₂(H) acts on U/Z, where U is the H-conjugate span of ZS. Faithfulness
on the component orbit is a separate F.9.18(2) obligation. -/
theorem local_quadratic_actor
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z)
    (hq : quadraticRatio a.representation ≤ 2) :
    ∃ A : Subgroup (H ⧸ pCore 2 H), IsElementaryTwo A ∧
      IsQuadratic a.representation A ∧ fixedCodim a.representation A ≤ 2 * rank A :=
  exists_quadratic_actor_of_ratio_le_two a.representation hq

/-- The faithful-image version of the F.9.18(6) step on the actual local
quotient. The residual image, component orbit, quadratic actor and its
faithfulness are explicit; no reduced module list or FF exclusion is assumed. -/
theorem local_section_alternatives
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z)
    (W : Subrepresentation a.representation) (K T : Subgroup G)
    (A : Subgroup (H ⧸ pCore 2 H))
    (hK : Theory.GroupTheory.IsComponent (H ⧸ pCore 2 H) (actorImage H K))
    (horbit : conjugateSpanBy (actorImage H K) (actorImage H T) =
      actorImage H (residual H))
    (hA : IsElementaryTwo A ∧ IsQuadratic a.representation A ∧
      actionRatio a.representation A ≤ 2)
    (hfaith : A ⊓ centralizer (actorImage H (residual H) : Set (H ⧸ pCore 2 H)) = ⊥)
    (hW : W.toSubmodule ≠ ⊥)
    (hc : subspaceCommutator a.representation W.toSubmodule
      (actorImage H (residual H)) = W.toSubmodule) :
    W.toSubmodule = subspaceCommutator a.representation ⊤ (actorImage H (residual H)) ∨
    (IsFFModule (imageRepresentation W.toRepresentation) ∧
      IsFFModule (imageRepresentation W.quotientRepresentation)) ∨
      IsStrongFFModule (imageRepresentation W.toRepresentation) ∨
        IsStrongFFModule (imageRepresentation W.quotientRepresentation) := by
  have hb := (actionRatio_le_two_iff a.representation hA.1).mp hA.2.2
  simpa only [horbit] using faithful_image_ff_alternative_of_component_orbit
    a.representation W (actorImage H K) (actorImage H T) A hK hA.1 hb
    (by rwa [horbit]) hW (by rwa [horbit])

end Local

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
