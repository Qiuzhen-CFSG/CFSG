module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.MultiplicitySimple
public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Geometry
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Trio
public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Stellmacher.ElementaryAbelianMaxDefs

/-!
# The marked earlier algebra for the AS91 incidence construction

`LocalData` retains one original cubic quotient, its Sylow three-subgroup and
its constructed three-space. The point and line groups have their original
ambient embeddings, overlaps, Todd projection and quotient maps. The actual
Sylow two-subgroup has elementary Thompson subgroup E. Its image in the same
S/R marking is a Sylow subgroup of the alternating factor, whose action on
the original multiplicity space is identified with the binary natural SL₂(4)
action.

These are explicit earlier-section inputs to the conditional sections 5–6
construction. The record contains no residue charts, incidence, fusion,
generation or recognition conclusion. Its existence is an obligation of the
section 4 construction, not asserted here. Ambient simplicity, when needed,
is supplied separately by the original finite-simple recognition consumer.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (4.4)–(4.8), pp.597–599,
DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open LocalGeometry LocalGeometry.LocalSubgroups SourceRecognition
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
variable {G : Type*} [Group G] [Finite G] {z : G}
attribute [local instance] ThreeSpaceData.R_normal_in_S_intrinsic

/-- Earlier marked algebra, with every group embedded in the same ambient group. -/
structure LocalData (h : IsTypeJ4 z) where
  e : CubicAutomorphismQuotient (centralizer z ⧸ core z)
  X : Sylow 3 (CubicLift.subgroup e)
  d : ThreeSpaceData z e X
  P : PointData z
  cubic_eq : P.cubic = e
  L : LineData z P
  point_normalizer : normalizer (P.E : Set G) = P.M
  line_normalizer : L.G₂ = normalizer (d.space : Set G)
  K_image : L.K.map L.G₂.subtype = d.K
  S_image : L.S.map L.G₂.subtype = d.S
  T : Sylow 2 G
  sylow_le : (T : Subgroup G) ≤ centralizer z ⊓ P.M ⊓ L.G₂
  E_eq_maxJ : P.E = Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)
  space_le_E : d.space ≤ P.E
  E_le_S : P.E ≤ d.S
  alternatingSylow : Sylow 2 (alternatingGroup (Fin 5))
  /-- The original quotient map, with no replacement S₅ marking. -/
  E_quotient : (P.E.subgroupOf d.S).map
      ((d.SQuotientEquiv h).toMonoidHom.comp (QuotientGroup.mk' (d.R.subgroupOf d.S))) =
    (alternatingSylow : Subgroup (alternatingGroup (Fin 5))).map
      (alternatingGroup (Fin 5)).subtype
  trio : Trio
  sextet : Sextet
  line_image : (L.G₂.subgroupOf P.M).map P.projection = trioStabilizer trio
  plane_image : ((centralizer z).subgroupOf P.M).map P.projection = sextetStabilizer sextet
  marker_vector : P.vectorEmbedding (Multiplicative.ofAdd (MathieuCode.sextetVector sextet)) = z
  /-- Binary coordinates on the actual four-dimensional multiplicity space. -/
  naturalEquiv : letI := d.multiplicitySpace_elementary h
    Additive d.multiplicitySpace ≃ₗ[ZMod 2] Representation.SL2FourNatural.V
  alternatingEquiv : alternatingGroup (Fin 5) ≃* Representation.SL2FourNatural.SL
  natural_equivariant : ∀ (g : alternatingGroup (Fin 5)) (w : d.multiplicitySpace),
    naturalEquiv (Additive.ofMul (d.markedMultiplicityAction h g w)) =
      Representation.SL2FourNatural.action (alternatingEquiv g)
        (naturalEquiv (Additive.ofMul w))

end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
