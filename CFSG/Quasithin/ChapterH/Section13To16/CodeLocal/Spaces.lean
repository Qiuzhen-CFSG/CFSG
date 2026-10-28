module

public import CFSG.Quasithin.ChapterH.Section13To16.Defs
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.GroupTheory.SolvableResidual

/-!
# Literal spaces and centralizers for the native code calculations

These are the actual fixed and commutator spaces of the Golay quotient.
The residual is taken inside the sextet stabilizer before mapping to M24;
the involution two-core is taken inside its centralizer in the same way.
No dimension, chief-factor, orthogonal-form, or centralizer assertion is
part of these definitions.

In the source notation the sextet fixed and residual spaces are V4 and V10,
the octad moved space is V5, and its intersection with the involution fixed
space is Vz. Proving these identifications and all their dimensions remains
the work of the local representation theorems.

Source: Aschbacher--Smith, H.16.1--2, printed pp.402--403.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterH.Section13To16

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender

/-- The source sextet fixed space V4. -/
noncomputable def codeSextetFixed (S : Sextet) : Submodule (ZMod 2) MathieuCode.Code :=
  fixedSpace MathieuCode.codeRepresentation (sextetKernel S)

/-- The source V10 uses the intrinsic solvable residual of the sextet stabilizer. -/
noncomputable def codeSextetResidualSpace (S : Sextet) :
    Submodule (ZMod 2) MathieuCode.Code :=
  subspaceCommutator MathieuCode.codeRepresentation ⊤
    ((Subgroup.solvableResidual (sextetStabilizer S)).map (sextetStabilizer S).subtype)

/-- The actual octad-kernel commutator space, to be identified with source V5. -/
noncomputable def codeOctadMoved (O : Octad) : Submodule (ZMod 2) MathieuCode.Code :=
  subspaceCommutator MathieuCode.codeRepresentation ⊤ (octadKernel O)

/-- Fixed vectors of the literal actor z in the native code. -/
noncomputable def codeInvolutionFixed (z : M24) : Submodule (ZMod 2) MathieuCode.Code :=
  fixedSpace MathieuCode.codeRepresentation (Subgroup.zpowers z)

/-- The actual intersection defining source Vz once V5 is identified. -/
noncomputable def codeOctadInvolutionFixed (O : Octad) (z : M24) :
    Submodule (ZMod 2) MathieuCode.Code :=
  codeOctadMoved O ⊓ codeInvolutionFixed z

/-- Source Pz, using the two-core intrinsic to the involution centralizer. -/
noncomputable def codeInvolutionCore (z : M24) : Subgroup M24 :=
  (pCore 2 (Subgroup.centralizer ({z} : Set M24))).map
    (Subgroup.centralizer ({z} : Set M24)).subtype

/-- Source D is the pointwise centralizer of Vz in the entire native M24. -/
noncomputable def codeOctadInvolutionCentralizer (O : Octad) (z : M24) : Subgroup M24 :=
  subspaceKernel MathieuCode.codeRepresentation (codeOctadInvolutionFixed O z) ⊤

end CFSG.Quasithin.ChapterH.Section13To16
