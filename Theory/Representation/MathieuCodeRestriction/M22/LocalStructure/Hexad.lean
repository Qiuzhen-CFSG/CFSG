module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.FixedSpaces
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CodeLine
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.DualSpaces

/-!
# Fixed-space and dual-space clauses for the marked M22 hexad

The inner and outer kernels remain the mapped intrinsic two-cores defined in
`LocalStructure`. Their comparison with the octad pointwise kernel and the
H.14 displacement four are explicit earlier inputs. M24 fixed-space inputs
are also explicit. The quotient and duality theorems prove the rank-five
cocode fixed space, the avoidance bound four, the xi hyperplane, the common
fixed space of noncyclic subgroups, the code fixed line, and the rank-five
code commutator.

The action and chief-flag transfers are assembled in the extension
`Hexad.Assembly`, which constructs their intermediate cocode witnesses.
This module remains the shared scalar-input boundary, avoiding cyclic imports.
The earlier M24, H.14 and quintet inputs must still be discharged by their
source-theorem owners.

Source: Aschbacher--Smith, H.15.2 and H.16.4, printed pp.398--399,403,
combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
namespace MathieuCode.Hexad

/-- Precisely the M24 scalar fixed-space statements used in the quotient
transfer. These concern the eleven-dimensional cocode, not its M22 quotient. -/
structure AmbientFixedInput (O : Octad) : Prop where
  fixed_finrank : Module.finrank (ZMod 2)
    (fixedSpace cocodeRepresentation (octadPointwiseKernel O)) = 6
  displacement : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
    fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4
  xi_codim : Module.finrank (ZMod 2)
    (Cocode ⧸ fixedSpaceSpan cocodeRepresentation (octadPointwiseKernel O)) = 1
  noncyclic_fixed : ∀ A : Subgroup M24, A ≤ octadPointwiseKernel O → ¬ IsCyclic A →
    fixedSpace cocodeRepresentation A = fixedSpace cocodeRepresentation (octadPointwiseKernel O)

abbrev OuterRestrictionInput (O : Octad) : Prop :=
  RestrictionInput (MonoidHom.id m22PairStabilizer) (m22OuterHexadKernel O) O

abbrev InnerRestrictionInput (O : Octad) : Prop :=
  RestrictionInput m22ToPairStabilizer (m22InnerHexadKernel O) O

/-- The outer input requires just the actual core image and earlier H.14 rank. -/
theorem outerRestrictionInput (O : Octad)
    (hK : (m22OuterHexadKernel O).map m22PairStabilizer.subtype = octadPointwiseKernel O)
    (hd : ∀ a ∈ m22OuterHexadKernel O, a ≠ 1 →
      fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers a) = 4) :
    OuterRestrictionInput O := ⟨Function.injective_id, hK, hd⟩

/-- The existing native embedding supplies injectivity in the inner case. -/
theorem innerRestrictionInput (O : Octad)
    (hK : (m22InnerHexadKernel O).map m22Embedding = octadPointwiseKernel O)
    (hd : ∀ a ∈ m22InnerHexadKernel O, a ≠ 1 →
      fixedCodim m22CocodeRepresentation (Subgroup.zpowers a) = 4) :
    InnerRestrictionInput O := by
  refine ⟨?_, hK, hd⟩
  intro a b hab
  exact m22Embedding_injective (congrArg Subtype.val hab)

end MathieuCode.Hexad
