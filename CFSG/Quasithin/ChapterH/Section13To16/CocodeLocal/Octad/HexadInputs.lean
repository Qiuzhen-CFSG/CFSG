module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Octad.Source
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.Centralizers
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.Transvections.Quotients

/-!
# Discharging the earlier M24 inputs of the hexad transfer

The established octad dynamics supplies the fixed-space, rank and parity
premises required by the M22 quotient construction. The quotient comparison
is the identity on cocode representatives; it transports the full transvection
identification and its conjugation formula to the literal fixed-space quotient
used by the hexad consumer. Native involution fusion supplies the pointwise
centralizer premise for every nonidentity kernel element.

Source: Aschbacher--Smith H.15.2(2--6), printed pp.398--399.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode MathieuCode.CocodeOctad Representation.BinaryOffender
open MathieuCode.Hexad.CocodeAction.Transvections
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal

/-- Every nonidentity octad-kernel element is in the native octad-fixing class. -/
theorem octadKernel_isConj_z (O : Octad) (z : M24)
    (hz : z ∈ octadPointwiseKernel O) (hne : z ≠ 1) :
    IsConj CocodeOctad.Involutions.z z := by
  have hzK : z ∈ octadKernel O := octadKernel_eq_pointwise O ▸ hz
  let _ := octadKernel_elementary O
  have hs : (⟨z, hzK⟩ : octadKernel O) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (octadKernel O)) _
  apply CocodeOctad.Involutions.isConj_z_of_fixedPoint
  · exact orderOf_eq_prime (congrArg Subtype.val hs) hne
  · obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < O.val.card by
      rw [m24Blocks_card _ O.property]; decide)
    exact ⟨i, (mem_octadPointwiseKernel O z).mp hz i hi⟩

/-- All scalar M24 premises of the actual M22 cocode quotient are proved. -/
theorem hexadAmbientFixedInput (O : Octad) : Hexad.AmbientFixedInput O where
  fixed_finrank := by rw [Dynamics.octad_fixedSpace]; exact finrank_supportedPairSpace O
  displacement := Dynamics.cyclic_fixedCodim O
  xi_codim := by
    rw [Dynamics.octad_fixedSpaceSpan]
    exact finrank_quotient_octadHyperplane O
  noncyclic_fixed A hA hn := by
    rw [Dynamics.octad_fixedSpace, Dynamics.octad_noncyclic_fixedSpace O A hA hn]

/-- The ambient pointwise-centralizer premise, with native class coverage discharged. -/
theorem hexadAmbientCentralizerInput (O : Octad) : Hexad.CocodeAction.AmbientCentralizerInput O where
  centralizer z hz hne := CocodeOctad.Involutions.pointwiseCentralizer_of_isConj_z z
    (octadKernel_isConj_z O z hz hne)

/-- Identity on representatives between the geometric and source quotients. -/
def octadSourceQuotientEquiv (O : Octad) :
    (Cocode ⧸ supportedPairSpace O.val) ≃ₗ[ZMod 2] (Cocode ⧸ ambientFixed O) :=
  Submodule.quotEquivOfEq _ _ (Dynamics.octad_fixedSpace O).symm

@[simp] theorem octadSourceQuotientEquiv_mk (O : Octad) (v : Cocode) :
    octadSourceQuotientEquiv O ((supportedPairSpace O.val).mkQ v) =
      (ambientFixed O).mkQ v := rfl

theorem octadSourceQuotientEquiv_equivariant (O : Octad) (g : octadStabilizer O)
    (x : Cocode ⧸ supportedPairSpace O.val) :
    octadSourceQuotientEquiv O (Dynamics.quotientRepresentation O g x) =
      ambientAction O g (octadSourceQuotientEquiv O x) := by
  obtain ⟨v, rfl⟩ := (supportedPairSpace O.val).mkQ_surjective x
  rfl

theorem octadSourceQuotientEquiv_map_axis (O : Octad) :
    (Dynamics.Axis O).map (octadSourceQuotientEquiv O).toLinearMap = ambientAxis O := by
  change ((octadHyperplane O).map (supportedPairSpace O.val).mkQ).map _ =
    (ambientSpan O).map (ambientFixed O).mkQ
  rw [ambientSpan, Dynamics.octad_fixedSpaceSpan, ← Submodule.map_comp]
  rfl

/-- The axis comparison retains the actual quotient maps. -/
def octadSourceAxisEquiv (O : Octad) : Dynamics.Axis O ≃ₗ[ZMod 2] ambientAxis O :=
  (octadSourceQuotientEquiv O).ofSubmodules _ _ (octadSourceQuotientEquiv_map_axis O)

@[simp] theorem octadSourceAxisEquiv_coe (O : Octad) (x : Dynamics.Axis O) :
    (octadSourceAxisEquiv O x).val = octadSourceQuotientEquiv O x.val := rfl

/-- The full native transvection theorem in the exact hexad consumer conventions. -/
def hexadAmbientTransvectionInput (O : Octad) : AmbientTransvectionInput O where
  fixed_le_span := by
    rw [ambientFixed, ambientSpan, Dynamics.octad_fixedSpace, Dynamics.octad_fixedSpaceSpan]
    exact supportedPairSpace_le_octadHyperplane O
  span_eq_parity := Dynamics.octad_fixedSpaceSpan O
  kernelEquiv := (Dynamics.octadTransvectionEquiv O).trans
    (AddEquiv.toMultiplicative (octadSourceAxisEquiv O).toAddEquiv)
  action a v := by
    have h := congrArg (octadSourceQuotientEquiv O)
      (Dynamics.octadTransvectionEquiv_action O a v)
    change (ambientFixed O).mkQ (cocodeRepresentation a.val v) =
      (ambientFixed O).mkQ v + octadParity O v •
        octadSourceQuotientEquiv O (Dynamics.octadTransvectionEquiv O a).toAdd.val
    simpa only [map_add, map_smul, octadSourceQuotientEquiv_mk] using h
  conjugation g a := by
    change octadSourceQuotientEquiv O
      (Dynamics.octadTransvectionEquiv O (Dynamics.kernelConjugate O g a)).toAdd.val =
      ambientAction O g (octadSourceQuotientEquiv O (Dynamics.octadTransvectionEquiv O a).toAdd.val)
    rw [Dynamics.octadTransvectionEquiv_conjugation, octadSourceQuotientEquiv_equivariant]

end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
