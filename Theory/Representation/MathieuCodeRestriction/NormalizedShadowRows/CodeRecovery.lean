module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeHexacode

/-!
# Hexacode recovery on the literal native code section

The existing raw Golay recovery kills the constant line, so it descends to
the ten-dimensional native even-code hyperplane. Its kernel is precisely
the fixed four-space of the same sextet core. The descended surjection
intertwines the full sextet stabilizer with its actual hexacode quotient,
including the central cubic of the even hexacode automorphism group.

Source: Aschbacher--Smith H.16.1(3) and 8.2.8(5), printed pp.402,718,
refs/quasithin.pdf. The recovery and affine action are the licensed ATLAS
port by Gerald Höhn and ATLAS contributors, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS.txt.
-/

public section
open Atlas.Codes Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode.SextetLayers.CoordinateTransport
namespace MathieuCode.NormalizedShadowRows.CodeHexacode
noncomputable section

/-- Quotienting the raw even Golay subcode by the same constant line. -/
@[expose] def evenProjection (S : Sextet) : C0 →ₗ[Bit] evenCode S :=
  ((codeLine.mkQ.comp (golayCoordinates S).toLinearMap).comp
    (C0.inclusion C0_le_golay)).codRestrict (evenCode S) (fun w =>
      ⟨golayCoordinates S (C0.inclusion C0_le_golay w),
        ⟨C0.inclusion C0_le_golay w,w.property,rfl⟩,rfl⟩)

lemma evenProjection_surjective (S : Sextet) : Function.Surjective (evenProjection S) := by
  rintro ⟨v,⟨w,⟨z,hz,rfl⟩,rfl⟩⟩
  exact ⟨⟨z.val,hz⟩,rfl⟩

private lemma coordinate_value (S : Sextet) (w : C0) (p : Omega) :
    (golayCoordinates S (C0.inclusion C0_le_golay w)).val ((nativeMarking S).pointEquiv p) = w.val p := by
  change w.val ((nativeMarking S).pointEquiv.symm ((nativeMarking S).pointEquiv p)) = w.val p
  rw [Equiv.symm_apply_apply]

/-- Recovery vanishes precisely on the original native fixed four-space. -/
lemma projection_mem_fixed_iff (S : Sextet) (w : C0) :
    (evenProjection S w).val ∈ CodeFlags.sextetCodeSpace S ↔ recoverHex w = 0 := by
  change codeLine.mkQ (golayCoordinates S (C0.inclusion C0_le_golay w)) ∈ _ ↔ _
  rw [CodeFlags.sextetCodeSpace_mk_iff]
  constructor
  · intro hc
    apply Subtype.ext
    funext i
    rw [recoverHex_blocks]
    have hb : (fun k => w.val (i,k)) = fun _ => w.val (i,0) := by
      funext k
      rw [←coordinate_value S w (i,k),←coordinate_value S w (i,0)]
      exact hc ((nativeMarking S).partEquiv i).val ((nativeMarking S).partEquiv i).property
        _ (((nativeMarking S).mem_part (i,k) i).mpr rfl)
        _ (((nativeMarking S).mem_part (i,0) i).mpr rfl)
    rw [hb,blockDecode_constant]
    rfl
  · intro hz B hB x hx y hy
    obtain ⟨r,hr,he⟩ := (recoverHex_kernel w).mp hz
    obtain ⟨i,hi⟩ := (nativeMarking S).partEquiv.surjective ⟨B,hB⟩
    have hxi : ((nativeMarking S).pointEquiv.symm x).1 = i := by
      apply ((nativeMarking S).mem_part _ i).mp
      simpa only [Equiv.apply_symm_apply,hi] using hx
    have hyi : ((nativeMarking S).pointEquiv.symm y).1 = i := by
      apply ((nativeMarking S).mem_part _ i).mp
      simpa only [Equiv.apply_symm_apply,hi] using hy
    change w.val ((nativeMarking S).pointEquiv.symm x) = w.val ((nativeMarking S).pointEquiv.symm y)
    rw [←he]
    change r (hexIndexEquiv ((nativeMarking S).pointEquiv.symm x).1) =
      r (hexIndexEquiv ((nativeMarking S).pointEquiv.symm y).1)
    rw [hxi,hyi]

private lemma projection_ker_le (S : Sextet) :
    (evenProjection S).ker ≤ recoverHex.ker := by
  intro w hw
  apply (projection_mem_fixed_iff S w).mp
  change evenProjection S w = 0 at hw
  rw [hw]
  exact (CodeFlags.sextetCodeSpace S).zero_mem

/-- Hexacode recovery on the literal ten-dimensional code hyperplane. -/
def evenRecovery (S : Sextet) : evenCode S →ₗ[Bit] hexacode :=
  (((evenProjection S).ker).liftQ recoverHex (projection_ker_le S)).comp
    ((evenProjection S).quotKerEquivOfSurjective (evenProjection_surjective S)).symm.toLinearMap

lemma evenRecovery_projection (S : Sextet) (w : C0) :
    evenRecovery S (evenProjection S w) = recoverHex w := by
  unfold evenRecovery
  rw [LinearMap.comp_apply]
  change (evenProjection S).ker.liftQ recoverHex (projection_ker_le S)
    (((evenProjection S).quotKerEquivOfSurjective (evenProjection_surjective S)).symm
      (evenProjection S w)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

lemma evenRecovery_surjective (S : Sextet) : Function.Surjective (evenRecovery S) := by
  intro h
  obtain ⟨w,rfl⟩ := recoverHex_surjective h
  exact ⟨evenProjection S w,evenRecovery_projection S w⟩

lemma evenRecovery_kernel (S : Sextet) (w : evenCode S) :
    evenRecovery S w = 0 ↔ w.val ∈ CodeFlags.sextetCodeSpace S := by
  obtain ⟨v,rfl⟩ := evenProjection_surjective S w
  rw [evenRecovery_projection,projection_mem_fixed_iff]

/-- The quotient recovery retains the actual full sextet action. -/
lemma evenRecovery_equivariant (S : Sextet) (g : sextetStabilizer S)
    (w : evenCode S) (hw : codeRepresentation g.val w.val ∈ evenCode S) :
    evenRecovery S ⟨codeRepresentation g.val w.val,hw⟩ =
      hexAction (nativeQuotient S g) (evenRecovery S w) := by
  obtain ⟨v,rfl⟩ := evenProjection_surjective S w
  obtain ⟨s,rfl⟩ := (nativeStabilizerEquiv S).surjective g
  have he : (⟨codeRepresentation (nativeStabilizerEquiv S s).val (evenProjection S v).val,hw⟩ : evenCode S) =
      evenProjection S (sextetC0Action s v) := by
    apply Subtype.ext
    change codeRepresentation (nativeStabilizerEquiv S s).val
      (codeLine.mkQ (golayCoordinates S (C0.inclusion C0_le_golay v))) = _
    rw [codeRepresentation_mk,←golayCoordinates_equivariant]
    rfl
  rw [he,evenRecovery_projection,evenRecovery_projection,nativeQuotient_apply,recoverHex_equivariant]

end
end MathieuCode.NormalizedShadowRows.CodeHexacode
