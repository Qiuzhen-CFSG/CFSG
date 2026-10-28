module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Orthogonal.M23.Linear
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Orthogonal.M23.SourceOrbit

/-!
# The faithful quadratic A7 quotient of an incident octad stabilizer

The relative kernel is exactly the intrinsic two-core. Its quotient embeds
in the M24 octad quotient and inherits that quotient's faithful action on
the supported quadratic space. The seven-coordinate map gives an actual
isomorphism with A7, with all maps specified on quotient representatives.

Source: Aschbacher--Smith, H.15.2(2), printed pp.398--399.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace MathieuCode.CocodeOctad

lemma m23_core_eq_comap (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    pCore 2 (m23OctadStabilizer O) = (pCore 2 (octadStabilizer O)).comap (m23ToOctad O) :=
  (sevenCoordinateAction_core O hO).trans (sevenCoordinateAction_ker O hO)

/-- The intrinsic M23 quotient identified with its literal alternating coordinate group. -/
def m23QuotientSevenEquiv (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (m23OctadStabilizer O ⧸ pCore 2 (m23OctadStabilizer O)) ≃*
      alternatingGroup (octadSeven O) :=
  (QuotientGroup.quotientMulEquivOfEq (sevenCoordinateAction_core O hO)).trans
    (quotientSevenEquiv O hO)

lemma m23QuotientSevenEquiv_mk (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (g : m23OctadStabilizer O) :
    (m23QuotientSevenEquiv O hO (QuotientGroup.mk g)).val = sevenCoordinateAction O hO g := rfl

/-- A numbering of the actual seven unfixed coordinates. -/
def sevenIndexEquiv (O : Octad) (hO : (0 : Fin 24) ∈ O.val) : octadSeven O ≃ Fin 7 :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, octadSeven_card O hO])

/-- A genuine equivalence with the standard alternating group of degree seven. -/
def m23QuotientA7Equiv (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (m23OctadStabilizer O ⧸ pCore 2 (m23OctadStabilizer O)) ≃*
      alternatingGroup (Fin 7) :=
  (m23QuotientSevenEquiv O hO).trans (sevenIndexEquiv O hO).altCongrHom

lemma m23QuotientA7Equiv_mk (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (g : m23OctadStabilizer O) :
    (m23QuotientA7Equiv O hO (QuotientGroup.mk g)).val =
      (sevenIndexEquiv O hO).permCongr (sevenCoordinateAction O hO g) := rfl

/-- The quotient map induced by the literal inclusion in the M24 octad stabilizer. -/
def m23QuotientEmbedding (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (m23OctadStabilizer O ⧸ pCore 2 (m23OctadStabilizer O)) →*
      (octadStabilizer O ⧸ pCore 2 (octadStabilizer O)) :=
  QuotientGroup.map _ _ (m23ToOctad O) (m23_core_eq_comap O hO).le

lemma m23QuotientEmbedding_mk (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (g : m23OctadStabilizer O) :
    m23QuotientEmbedding O hO (QuotientGroup.mk g) =
      QuotientGroup.mk (m23ToOctad O g) := rfl

lemma m23QuotientEmbedding_injective (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    Function.Injective (m23QuotientEmbedding O hO) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [m23QuotientEmbedding, QuotientGroup.ker_map, ← m23_core_eq_comap O hO,
    QuotientGroup.map_mk'_self]

/-- The faithful quotient action on the already constructed quadratic form. -/
def m23QuotientIsometryAction (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (m23OctadStabilizer O ⧸ pCore 2 (m23OctadStabilizer O)) →*
      Atlas.Order20160A8.isometrySubgroup (quadratic O) :=
  (quotientIsometryAction O).comp (m23QuotientEmbedding O hO)

lemma m23QuotientIsometryAction_injective (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    Function.Injective (m23QuotientIsometryAction O hO) :=
  (quotientIsometryAction_injective O).comp (m23QuotientEmbedding_injective O hO)

lemma m23QuotientIsometryAction_mk (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (g : m23OctadStabilizer O) (v : supportedPairSpace O.val) :
    (m23QuotientIsometryAction O hO (QuotientGroup.mk g)).val v =
      m23PairRepresentation O g v :=
  quotientIsometryAction_mk O (m23ToOctad O g) v

/-- The kernel of the literal linear action, as a relative subgroup. -/
lemma m23PairRepresentation_ker (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (m23PairRepresentation O).ker = pCore 2 (m23OctadStabilizer O) := by
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    have hi : m23QuotientIsometryAction O hO (QuotientGroup.mk g) = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      rw [m23QuotientIsometryAction_mk, hg]
      rfl
    have hm : (QuotientGroup.mk g : m23OctadStabilizer O ⧸ pCore 2 _) = 1 :=
      (m23QuotientIsometryAction_injective O hO) (hi.trans (map_one _).symm)
    exact (QuotientGroup.eq_one_iff g).mp hm
  · intro hg
    apply LinearMap.ext
    intro v
    rw [← m23QuotientIsometryAction_mk O hO, (QuotientGroup.eq_one_iff g).mpr hg, map_one]
    rfl

/-- The restricted action in the same split quadratic coordinates as the M24 action. -/
lemma m23_formEquiv_equivariant (O : Octad) (g : m23OctadStabilizer O)
    (x : ClassicalOrthogonal.VectorD 3 Bit) :
    formEquiv O ((splitAction O (m23ToOctad O g)).val x) =
      m23PairRepresentation O g (formEquiv O x) :=
  formEquiv_equivariant O (m23ToOctad O g) x

end MathieuCode.CocodeOctad
