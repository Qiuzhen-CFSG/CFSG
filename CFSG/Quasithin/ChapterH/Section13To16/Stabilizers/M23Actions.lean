module

public import Theory.Mathieu.M23.QuasithinGeometry.ChapterHLocalActions
public import CFSG.Quasithin.ChapterH.Section13To16.Defs

/-!
# The native M23 quintet and heptad conjugation modules

The literal quintet stabilizer modulo its intrinsic two-core is ΓL₂(4).
The two systematic F₄ coordinates identify its source kernel with the
natural plane, with the native conjugation and point embedding retained.

The literal marked heptad stabilizer has intrinsic two-core equal to the
restriction of the octad core through `MathieuCode.pointEmbedding`. Its
quotient is A7, and explicit binary coordinates intertwine its conjugation
on that core with the proved irreducible four-dimensional representation.

Source: Aschbacher–Smith, H.14.2(2–3), printed p.397. The hexacode
constructions and their ATLAS attribution are recorded in the imported
`ChapterHLocalActions` development.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterH.Section13To16
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M23Geometry MathieuCode
open ChapterHLocalActions
noncomputable section

/-- The source quintet kernel is the included intrinsic two-core. -/
theorem standardM23_quintet_core :
    m23QuintetKernel standardSextet =
      (pCore 2 CommonFour.quintetStabilizer).map
        CommonFour.quintetStabilizer.subtype := rfl

/-- The literal source quintet quotient is the full semilinear group ΓL₂(4). -/
def standardM23_quintet_quotient_equiv :
    (m23QuintetStabilizer standardSextet ⧸ pCore 2 (m23QuintetStabilizer standardSextet)) ≃*
      HexSemilinear.Gamma := quintetQuotientEquiv

/-- Natural F₄-plane coordinates on the literal source kernel inside native M23. -/
def standardM23_quintet_kernel_equiv :
    Multiplicative Representation.SL2FourNatural.V ≃* m23QuintetKernel standardSextet :=
  quintetAmbientBinaryEquiv

/-- H.14.2(2): the source quotient acts naturally on its actual kernel by conjugation. -/
theorem standardM23_quintet_kernel_action (g : m23QuintetStabilizer standardSextet)
    (v : Representation.SL2FourNatural.V) :
    g.val * (standardM23_quintet_kernel_equiv (Multiplicative.ofAdd v)).val * g.val⁻¹ =
      (standardM23_quintet_kernel_equiv (Multiplicative.ofAdd
        (HexSemilinear.natural (standardM23_quintet_quotient_equiv (QuotientGroup.mk g))
          v))).val :=
  quintetAmbientBinaryEquiv_conjugation g v

/-- The same source action is explicitly matrix multiplication after a field automorphism. -/
theorem standardM23_quintet_kernel_matrix_action (g : m23QuintetStabilizer standardSextet)
    (v : Representation.SL2FourNatural.V) :
    let a := standardM23_quintet_quotient_equiv (QuotientGroup.mk g)
    g.val * (standardM23_quintet_kernel_equiv (Multiplicative.ofAdd v)).val * g.val⁻¹ =
      (standardM23_quintet_kernel_equiv
        (Multiplicative.ofAdd (a.left.val.mulVec (fun i => a.right (v i))))).val := by
  simpa only [HexSemilinear.natural_apply] using standardM23_quintet_kernel_action g v

/-- The source coordinates commute with the actual native point embedding. -/
theorem standardM23_quintet_kernel_pointEmbedding (v : Representation.SL2FourNatural.V) :
    pointEmbedding (standardM23_quintet_kernel_equiv (Multiplicative.ofAdd v)).val =
      (M24ChapterHStabilizers.SextetAction.ambientTranslationEquiv
        (Atlas.Codes.hexZeroInclusion QuintetHexacode.i0 (Multiplicative.ofAdd
          (Representation.Hexacode.ZeroNatural.vectorCoordinates.symm v)))).val :=
  quintetAmbientBinaryEquiv_pointEmbedding v

/-- The natural source module has field dimension two and binary dimension four. -/
theorem standardM23_quintet_module :
    Module.finrank Representation.SL2FourNatural.F Representation.SL2FourNatural.V = 2 ∧
      Module.finrank (ZMod 2) Representation.SL2FourNatural.V = 4 :=
  quintet_module_dimensions

/-- The restricted ambient octad kernel is the intrinsic heptad two-core. -/
theorem standardM23_heptad_core :
    m23OctadKernel standardOctad =
      (pCore 2 CommonFour.markedHeptadStabilizer).map
        CommonFour.markedHeptadStabilizer.subtype :=
  CommonFour.octad_core_comap.trans CommonFour.heptad_core_eq.symm

/-- The heptad quotient by its intrinsic two-core is the genuine A7. -/
def standardM23_heptad_quotient_equiv :
    (CommonFour.markedHeptadStabilizer ⧸ pCore 2 CommonFour.markedHeptadStabilizer) ≃*
      alternatingGroup (Fin 7) := sourceQuotientEquiv

/-- The coordinates land in the literal source kernel inside native M23. -/
def standardM23_heptad_kernel_equiv :
    Multiplicative Four ≃* m23OctadKernel standardOctad :=
  (sourceBinaryEquiv.trans
    ((pCore 2 CommonFour.markedHeptadStabilizer).equivMapOfInjective
      CommonFour.markedHeptadStabilizer.subtype
      CommonFour.markedHeptadStabilizer.subtype_injective)).trans
    (MulEquiv.subgroupCongr standardM23_heptad_core.symm)

/-- H.14.2(3): these coordinates retain the actual ambient conjugation action. -/
theorem standardM23_heptad_kernel_action (g : CommonFour.markedHeptadStabilizer)
    (v : Four) :
    g.val * (standardM23_heptad_kernel_equiv (Multiplicative.ofAdd v)).val * g.val⁻¹ =
      (standardM23_heptad_kernel_equiv (Multiplicative.ofAdd
        (sourceQuotientRepresentation (QuotientGroup.mk g) v))).val :=
  congrArg Subtype.val (sourceBinaryEquiv_conjugation g v)

/-- The source kernel module has binary dimension four and is irreducible. -/
theorem standardM23_heptad_module :
    Module.finrank (ZMod 2) Four = 4 ∧
      Representation.IsIrreducible sourceQuotientRepresentation :=
  ⟨by simp [Four], sourceQuotientRepresentation_irreducible⟩

end
end CFSG.Quasithin.ChapterH.Section13To16
