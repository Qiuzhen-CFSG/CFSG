module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Dynamics.Basic
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Dynamics.FixedSpaces
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Dynamics.Transvections

/-!
# Fixed spaces and full transvection action of native octad kernels

Native exterior moments give the literal five-dimensional quotient by the
octad pair space and identify its transvection axis with the elementary
abelian kernel, equivariantly under the octad stabilizer. The checked cyclic
fixed dimension gives the common fixed spaces and identifies their span with
the octad-parity hyperplane. The cyclic dimension is discharged using native
code calculations and cyclic code/cocode duality. Earlier conditional helpers
are re-exported from `Dynamics.Basic` without changing their interfaces.

Source: Aschbacher--Smith, H.15.2(2,4--6), printed pp.398--399.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
namespace MathieuCode.CocodeOctad

lemma intrinsicOctadKernel_eq_pointwise (O : Octad) :
    intrinsicOctadKernel O = octadPointwiseKernel O := octad_core_map_eq_pointwise O

lemma intrinsicOctadKernel_fixedSpace (O : Octad) :
    fixedSpace cocodeRepresentation (intrinsicOctadKernel O) = octadPairSpace O := by
  rw [intrinsicOctadKernel_eq_pointwise]
  exact Dynamics.octad_fixedSpace O

lemma intrinsicOctadKernel_noncyclic_fixedSpace (O : Octad) (A : Subgroup M24)
    (hA : A ≤ intrinsicOctadKernel O) (hnc : ¬ IsCyclic A) :
    fixedSpace cocodeRepresentation A = octadPairSpace O := by
  rw [intrinsicOctadKernel_eq_pointwise] at hA
  exact Dynamics.octad_noncyclic_fixedSpace O A hA hnc

lemma intrinsicOctadKernel_fixedSpaceSpan (O : Octad) :
    fixedSpaceSpan cocodeRepresentation (intrinsicOctadKernel O) = octadHyperplane O := by
  rw [intrinsicOctadKernel_eq_pointwise]
  exact Dynamics.octad_fixedSpaceSpan O

lemma intrinsicOctadKernel_cyclic_fixedCodim (O : Octad) (z : intrinsicOctadKernel O)
    (hz : z.val ≠ 1) : fixedCodim cocodeRepresentation (Subgroup.zpowers z.val) = 4 :=
  Dynamics.cyclic_fixedCodim O z.val
    (intrinsicOctadKernel_eq_pointwise O ▸ z.property) hz

end MathieuCode.CocodeOctad
