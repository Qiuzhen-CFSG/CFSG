module

public import Stellmacher.PushingUp.ActionQuotientSL2Frattini
public import Stellmacher.PushingUp.CriticalPairCommutator
public import Stellmacher.PushingUp.SL2TwoModule
public import Stellmacher.PushingUp.VertexZLocalModule
public import Stellmacher.SectionTwo.QuotientModuleTransport

/-!
# Canonical critical-pair action data

This module fixes the production-facing objects used in Stellmacher,
*Pushing up*, Arch. Math. 46 (1986), Lemma (2.2), journal p.11, specialized
to `p = 2` and `n = 1`.  At a graph vertex `a`, the chosen Sylow
2-subgroup of `G_a` determines the canonical Section 2 module `V`, its
centralizer `C`, the faithful quotient `G_a/C`, and the named quotient
conjugation action.  The graph subgroup at the opposite endpoint maps to the
source actor `Tbar`; the intrinsic center intersection is recorded as an
actual subgroup of `V`.

The module also states three proposition-valued packages.  `ActionInputs`
is the exact collection supplied by the critical-distance, centralizer,
standing-(A), and action-quotient arguments, including the path containment
`Z_a ≤ G_{a'}` needed by the opposite fixed-space calculation.
`FixedSpaceData` records the
two fixed-point transports, the action-commutator transport, and the two
relative-index cardinal identities used to orient the source inequality.
`Conclusion` is the literal four-clause output of (2.2).  Its existential
group equivalence is shared by the `SL₂(2)` identification and the natural
module assertion; naturality is not weakened to a cardinality statement.

All canonical constructions are abbreviations, so later proof modules use one
definitionally identical quotient and action.  Normality of the action
centralizer follows from normality of the normal closure defining the canonical module.  The centralizer bridge identifies
this internal action kernel with the local ambient centralizer, by transporting
commutation across the subtype map identifying the module with `Z_a`.
-/

namespace Stellmacher.PushingUp

open scoped Pointwise
open AmalgamGraph

universe u

variable {M : Type u} [Group M] [Finite M]

public abbrev VertexGroup (S : Subgroup M) (a : Vertex S) := stabilizer S a

public noncomputable abbrev vertexSylow (S : Subgroup M) (a : Vertex S) :
    Sylow 2 (VertexGroup S a) := default

public noncomputable abbrev vertexModule (S : Subgroup M) (a : Vertex S) :
    Subgroup (VertexGroup S a) :=
  Stellmacher.SectionTwo.vSubgroup (vertexSylow S a)

public noncomputable abbrev vertexActionCentralizer
    (S : Subgroup M) (a : Vertex S) : Subgroup (VertexGroup S a) :=
  Stellmacher.SectionTwo.cSubgroup (vertexSylow S a)

public noncomputable instance vertexActionCentralizer_normal
    (S : Subgroup M) (a : Vertex S) :
    (vertexActionCentralizer S a).Normal := by
  let _ : (Stellmacher.SectionTwo.vSubgroup (vertexSylow S a)).Normal := by
    rw [Stellmacher.SectionTwo.vSubgroup]
    exact Subgroup.normalClosure_normal
  dsimp [vertexActionCentralizer, Stellmacher.SectionTwo.cSubgroup]
  exact Subgroup.normal_centralizer

public noncomputable abbrev VertexActionQuotient
    (S : Subgroup M) (a : Vertex S) :=
  VertexGroup S a ⧸ vertexActionCentralizer S a

public noncomputable abbrev vertexActionQuotientMap
    (S : Subgroup M) (a : Vertex S) :
    VertexGroup S a →* VertexActionQuotient S a :=
  QuotientGroup.mk' (vertexActionCentralizer S a)

public noncomputable abbrev vertexQuotientConjugationAction
    (S : Subgroup M) (a : Vertex S) :
    MulDistribMulAction (VertexActionQuotient S a) (vertexModule S a) :=
  Stellmacher.SectionTwo.quotientConjugationAction
    (vertexSylow S a) (vertexActionQuotientMap S a)
    (QuotientGroup.mk'_surjective (vertexActionCentralizer S a))
    (QuotientGroup.ker_mk' (vertexActionCentralizer S a))

public noncomputable abbrev oppositeImage
    (S : Subgroup M) (a a' : Vertex S)
    (_ha' : vertexZ S a' ≤ stabilizer S a) :
    Subgroup (VertexActionQuotient S a) :=
  ((vertexZ S a').subgroupOf (stabilizer S a)).map
    (vertexActionQuotientMap S a)

/-- The literal denominator `Z_a ∩ Z(G_a)` inside the local module. -/
public noncomputable abbrev vertexCenterPart
    (S : Subgroup M) (a : Vertex S) : Subgroup (vertexModule S a) :=
  (Subgroup.center (VertexGroup S a)).comap (vertexModule S a).subtype

/-- The action kernel of the local module is the ambient centralizer of `Z_a`. -/
public theorem vertexActionCentralizer_eq_vertexCentralizerLocal
    (S : Subgroup M) (a : Vertex S) :
    vertexActionCentralizer S a = vertexCentralizerLocal S a := by
  let G := stabilizer S a
  let V : Subgroup G := vertexModule S a
  have hVmap : V.map G.subtype = vertexZ S a := by
    simpa [V, G, vertexModule, vertexSylow, VertexGroup] using
      vertexZ_eq_local_vSubgroup S a
  ext x
  rw [mem_vertexCentralizerLocal_iff]
  change x ∈ Subgroup.centralizer (V : Set G) ↔
    (x : FreeAmalgam S) ∈
      Subgroup.centralizer (vertexZ S a : Set (FreeAmalgam S))
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx z hz
    rw [← hVmap] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact congrArg G.subtype (hx v hv)
  · intro hx v hv
    apply G.subtype_injective
    exact hx (v : FreeAmalgam S)
      (by rw [← hVmap]; exact Subgroup.mem_map_of_mem G.subtype hv)


namespace CriticalPairSL2Two

/-- The quotient-action hypotheses assembled from (1.3), (1.4), and standing
condition (A), before the finite module theorem is applied. -/
public structure ActionInputs (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (hV : IsElementaryAbelian 2 (vertexModule S a)) : Prop where
  critical : CriticalPairCommutator.Conclusion S a a'
  oppositeCentralizer_odd : CriticalVertexCentralizer.Conclusion S a'
  left_Z_le_right_stabilizer : vertexZ S a ≤ stabilizer S a'
  left_Z_le_coreOmega :
    vertexZ S a ≤ omegaOneCenterAmbient (vertexTwoCore S a)
  right_Z_le_coreOmega :
    vertexZ S a' ≤ omegaOneCenterAmbient (vertexTwoCore S a')
  quotientCore_eq_bot : pCore 2 (VertexActionQuotient S a) = ⊥
  quotientNestedSL2 :
    IsSL2Two
      (((VertexActionQuotient S a) ⧸ pCore 2 (VertexActionQuotient S a)) ⧸
        frattini ((VertexActionQuotient S a) ⧸
          pCore 2 (VertexActionQuotient S a)))
  quotient_not_two : ¬ IsPGroup 2 (VertexActionQuotient S a)
  oppositeImage_isPGroup : IsPGroup 2 (oppositeImage S a a' ha')
  oppositeImage_ne_bot : oppositeImage S a a' ha' ≠ ⊥
  oppositeImage_quadratic :
    let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
    let _ := vertexQuotientConjugationAction S a
    commutatorAction₂ (oppositeImage S a a' ha') (vertexModule S a) = ⊥

/-- Fixed-space, action-commutator, and cardinal transports for the chosen
orientation of a critical pair. -/
public structure FixedSpaceData (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (hV : IsElementaryAbelian 2 (vertexModule S a)) : Prop where
  oppositeFixed_map :
    let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
    let _ := vertexQuotientConjugationAction S a
    ((FixedPoints.subgroup (oppositeImage S a a' ha')
        (vertexModule S a)).map (vertexModule S a).subtype).map
          (stabilizer S a).subtype =
      vertexZ S a ⊓ vertexTwoCore S a'
  globalFixed_eq_centerPart :
    let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
    let _ := vertexQuotientConjugationAction S a
    FixedPoints.subgroup (VertexActionQuotient S a) (vertexModule S a) =
      vertexCenterPart S a
  commutator_map :
    let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
    let _ := vertexQuotientConjugationAction S a
    ((commutatorAction (oppositeImage S a a' ha')
        (vertexModule S a)).map (vertexModule S a).subtype).map
          (stabilizer S a).subtype =
      ⁅vertexZ S a, vertexZ S a'⁆
  oppositeImage_card :
    Nat.card (oppositeImage S a a' ha') =
      (vertexZ S a' ⊓ vertexTwoCore S a).relIndex (vertexZ S a')
  fixedQuotient_card :
    let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
    let _ := vertexQuotientConjugationAction S a
    Nat.card ((vertexModule S a) ⧸
        FixedPoints.subgroup (oppositeImage S a a' ha')
          (vertexModule S a)) =
      (vertexZ S a ⊓ vertexTwoCore S a').relIndex (vertexZ S a)

/-- The exact four clauses of source (2.2); the same `ebarG` witnesses both
the group and natural-module conclusions. -/
public structure Conclusion (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (hV : IsElementaryAbelian 2 (vertexModule S a)) : Prop where
  sourceSylow :
    IsSylowSubgroupIn
      (vertexZ S a' ⊔ vertexTwoCore S a) (stabilizer S a)
  sl2AndNaturalModule :
    let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
    let _ := vertexQuotientConjugationAction S a
    ∃ ebarG : VertexActionQuotient S a ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      ∃ hC : IsInvariant (VertexActionQuotient S a) (vertexModule S a)
          (vertexCenterPart S a),
        letI := quotientMulDistribMulAction
          (A := VertexActionQuotient S a) (G := vertexModule S a)
          (vertexCenterPart S a) hC
        IsNaturalSL2TwoActionAlong
          (vertexModule S a ⧸ vertexCenterPart S a) ebarG
  sourceOmegaCenter :
    omegaOneCenterAmbient (vertexZ S a' ⊔ vertexTwoCore S a) =
      ⁅vertexZ S a, vertexZ S a'⁆ ⊔
        (vertexZ S a ⊓
          (Subgroup.center (VertexGroup S a)).map (stabilizer S a).subtype)

end CriticalPairSL2Two

end Stellmacher.PushingUp
