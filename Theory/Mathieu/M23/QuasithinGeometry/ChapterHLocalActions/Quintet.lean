module

public import Theory.Mathieu.M23.QuasithinGeometry.ChapterHLocalActions.HexSemilinear
public import Theory.Mathieu.M23.QuasithinGeometry.ChapterHLocalActions.QuintetHexacode

/-!
# The natural semilinear action on the native quintet core

The literal quintet stabilizer is the preimage of the standard sextet
stabilizer under `MathieuCode.pointEmbedding`. Compose its intrinsic
quotient identification with the genuine hexacode ΓL₂(4) equivalence.
The same two systematic F₄ coordinates identify its intrinsic two-core
with the additive natural plane, and intertwine full native conjugation
with matrix multiplication after a coordinatewise field automorphism.

The binary restriction has dimension four. Both the quotient and module
coordinates retain the native affine marking and the literal M23-to-M24
point embedding. All quotient, coverage and coordinate premises are
supplied by `QuintetHexacode` and `HexSemilinear`.

Source: Aschbacher–Smith, H.14.2(2), printed p.397 of the combined
1 March 2004 manuscript. The hexacode constructions and their ATLAS
attribution and license are recorded in the two imported modules.
-/

@[expose] public section

noncomputable section
open Atlas.Codes Representation
open Representation.Hexacode.ZeroNatural (vectorCoordinates)
open Sporadic.Mathieu Sporadic.Mathieu.M23Geometry
namespace Sporadic.Mathieu.M23Geometry.ChapterHLocalActions

/-- The literal quintet stabilizer modulo its intrinsic two-core is ΓL₂(4). -/
def quintetQuotientEquiv :
    (CommonFour.quintetStabilizer ⧸ pCore 2 CommonFour.quintetStabilizer) ≃*
      HexSemilinear.Gamma :=
  QuintetHexacode.quotientEquiv.trans HexSemilinear.modelEquiv

/-- The semilinear quotient map uses the native affine quotient on representatives. -/
theorem quintetQuotientEquiv_mk (g : CommonFour.quintetStabilizer) :
    quintetQuotientEquiv (QuotientGroup.mk g) =
      HexSemilinear.modelEquiv (QuintetHexacode.quotientHom g) := by
  exact congrArg HexSemilinear.modelEquiv (QuintetHexacode.quotientEquiv_mk g)

/-- The actual two systematic F₄ coordinates on the intrinsic native quintet core. -/
def quintetBinaryEquiv :
    Multiplicative SL2FourNatural.V ≃* pCore 2 CommonFour.quintetStabilizer :=
  (AddEquiv.toMultiplicative vectorCoordinates.symm.toAddEquiv).trans
    QuintetHexacode.translationEquiv

/-- The coordinates intertwine native conjugation with the full natural semilinear action. -/
theorem quintetBinaryEquiv_conjugation (g : CommonFour.quintetStabilizer)
    (v : SL2FourNatural.V) :
    g * (quintetBinaryEquiv (Multiplicative.ofAdd v)).val * g⁻¹ =
      (quintetBinaryEquiv (Multiplicative.ofAdd
        (HexSemilinear.natural (quintetQuotientEquiv (QuotientGroup.mk g)) v))).val := by
  change g * (QuintetHexacode.translationEquiv
    (Multiplicative.ofAdd (vectorCoordinates.symm v))).val * g⁻¹ =
      (QuintetHexacode.translationEquiv (Multiplicative.ofAdd (vectorCoordinates.symm
        (HexSemilinear.natural
          (HexSemilinear.modelEquiv (QuintetHexacode.quotientEquiv (QuotientGroup.mk g)))
          v)))).val
  rw [QuintetHexacode.translationEquiv_conjugation]
  have hv : hexZeroLinear QuintetHexacode.i0
      (QuintetHexacode.quotientEquiv (QuotientGroup.mk g)) (vectorCoordinates.symm v) =
      vectorCoordinates.symm (HexSemilinear.natural
        (HexSemilinear.modelEquiv (QuintetHexacode.quotientEquiv (QuotientGroup.mk g))) v) := by
    apply vectorCoordinates.injective
    rw [LinearEquiv.apply_symm_apply, ← HexSemilinear.modelEquiv_equivariant,
      LinearEquiv.apply_symm_apply]
  rw [hv]

/-- The natural semilinear action, regarded as a binary representation. -/
def quintetNaturalRepresentation : Representation (ZMod 2) HexSemilinear.Gamma
    SL2FourNatural.V where
  toFun a := (HexSemilinear.natural a).toLinearMap
  map_one' := congrArg LinearEquiv.toLinearMap HexSemilinear.natural.map_one
  map_mul' a b := congrArg LinearEquiv.toLinearMap (HexSemilinear.natural.map_mul a b)

/-- The representation of the intrinsic source quotient in these same coordinates. -/
def quintetQuotientRepresentation : Representation (ZMod 2)
    (CommonFour.quintetStabilizer ⧸ pCore 2 CommonFour.quintetStabilizer)
    SL2FourNatural.V :=
  quintetNaturalRepresentation.comp quintetQuotientEquiv.toMonoidHom

/-- The source module is a four-dimensional binary restriction of the F₄ plane. -/
theorem quintet_module_dimensions :
    Module.finrank SL2FourNatural.F SL2FourNatural.V = 2 ∧
      Module.finrank (ZMod 2) SL2FourNatural.V = 4 :=
  ⟨by simp [SL2FourNatural.V], SL2FourNatural.finrank_vector⟩

/-- The natural coordinates on the intrinsic core included in native M23. -/
def quintetAmbientBinaryEquiv : Multiplicative SL2FourNatural.V ≃*
    (pCore 2 CommonFour.quintetStabilizer).map CommonFour.quintetStabilizer.subtype :=
  quintetBinaryEquiv.trans ((pCore 2 CommonFour.quintetStabilizer).equivMapOfInjective
    CommonFour.quintetStabilizer.subtype CommonFour.quintetStabilizer.subtype_injective)

/-- The quotient representation is the actual ambient conjugation action. -/
theorem quintetAmbientBinaryEquiv_conjugation (g : CommonFour.quintetStabilizer)
    (v : SL2FourNatural.V) :
    g.val * (quintetAmbientBinaryEquiv (Multiplicative.ofAdd v)).val * g.val⁻¹ =
      (quintetAmbientBinaryEquiv (Multiplicative.ofAdd
        (quintetQuotientRepresentation (QuotientGroup.mk g) v))).val :=
  congrArg Subtype.val (quintetBinaryEquiv_conjugation g v)

/-- The coordinates retain the literal M23-to-M24 point embedding and sextet translations. -/
theorem quintetAmbientBinaryEquiv_pointEmbedding (v : SL2FourNatural.V) :
    MathieuCode.pointEmbedding (quintetAmbientBinaryEquiv (Multiplicative.ofAdd v)).val =
      (M24ChapterHStabilizers.SextetAction.ambientTranslationEquiv
        (hexZeroInclusion QuintetHexacode.i0
          (Multiplicative.ofAdd (vectorCoordinates.symm v)))).val := by
  calc
    _ = (QuintetHexacode.toSextet (QuintetHexacode.translationEquiv
        (Multiplicative.ofAdd (vectorCoordinates.symm v))).val).val :=
      (QuintetHexacode.toSextet_coe _).symm
    _ = _ := congrArg Subtype.val (QuintetHexacode.translationEquiv_toSextet _)

end Sporadic.Mathieu.M23Geometry.ChapterHLocalActions
