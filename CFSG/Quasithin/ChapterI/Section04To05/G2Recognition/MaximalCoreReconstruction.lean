module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCoreForm
public import Theory.GroupTheory.CentralCubicReconstruction

/-!
# Reconstructing the full original cubic cores and their actions

Conjugation by the original marked central involution fixes the cubic line
and inverts the quotient. Thus every quotient element has a unique inverted
lift, giving canonical coordinates on the full nonabelian core. The cocycle
is exactly the previously constructed commutator pairing. The whole original
Levi preserves these lifts, including its marked GL₂(3) coordinates.

A form-preserving comparison of quotient and line now constructs an actual
core equivalence. Because the line is the derived subgroup, compatibility
of the quotient actions suffices for compatibility of the full core actions;
there is no extra central discrepancy to solve. These are the original
quotient maps and original involution, on either side by factor swapping.

This removes the central-extension ambiguity in the endpoint comparison
for Aschbacher–Smith I.4.5, printed p.417. Constructing the Atlas quotient
comparisons compatibly on the whole middle and excluding the independent
strongly-three-embedded branch remain necessary. The literal Chapter14
application is Chapter14CoreReconstruction.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus
variable (t : CubicTorus c)

/-- The original marked involution supplies the central cubic extension data. -/
def cubicInvolutionExtension : CubicInvolutionExtension (cubicOddCore c t.x)
    (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) where
  quotient := QuotientGroup.mk' (cubicCoreLine c t.x)
  surjective := QuotientGroup.mk'_surjective _
  central := by rw [QuotientGroup.ker_mk']; exact cubicCoreLine_le_center c t.x
  cube := t.left_oddCore_cube
  involution := cubicOppositeAction c t.x ⟨t.z,(t.central_line ▸ mem_zpowers t.z).2⟩
  involutive := by
    intro v
    apply Subtype.ext
    change (t.z:G)*((t.z:G)*(v:G)*(t.z:G)⁻¹)*(t.z:G)⁻¹=(v:G)
    have hz : (t.z:G)*(t.z:G)=1 := by
      have hz' : t.z*t.z=1 := by simpa only [pow_two,t.z_order] using pow_orderOf_eq_one t.z
      exact congrArg Subtype.val hz'
    calc
      _ = ((t.z:G)*(t.z:G))*(v:G)*((t.z:G)*(t.z:G))⁻¹ := by group
      _ = (v:G) := by rw [hz,one_mul,inv_one,mul_one]
  fixed := by
    intro v hv
    rw [QuotientGroup.ker_mk'] at hv
    have hH : (v:G)∈c.H := (zpowers_le.mpr t.x.val.property) hv
    have hz := mem_centralizer_singleton_iff.mp (t.centralizer ▸ hH)
    apply Subtype.ext
    change (t.z:G)*(v:G)*(t.z:G)⁻¹=(v:G)
    rw [←hz,mul_inv_cancel_right]
  inverted := t.left_oddCore_quotient_inverted

/-- The unique lift inverted by the original central involution. -/
noncomputable def cubicInvertedSection
    (v : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) : cubicOddCore c t.x :=
  t.cubicInvolutionExtension.invertedSection v

@[simp] theorem cubicInvertedSection_quotient
    (v : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    QuotientGroup.mk' (cubicCoreLine c t.x) (t.cubicInvertedSection v)=v :=
  t.cubicInvolutionExtension.quotient_section v

/-- An explicit formula retaining the original ambient conjugation. -/
theorem cubicInvertedSection_mk (v : cubicOddCore c t.x) :
    (t.cubicInvertedSection (QuotientGroup.mk' (cubicCoreLine c t.x) v):G)=
      (v:G)⁻¹*((t.z:G)*(v:G)*(t.z:G)⁻¹) :=
  congrArg Subtype.val (t.cubicInvolutionExtension.section_quotient v)

theorem cubicInvertedSection_inverted (v : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    MulAut.conj (t.z:G) (t.cubicInvertedSection v:G)=(t.cubicInvertedSection v:G)⁻¹ :=
  congrArg Subtype.val (t.cubicInvolutionExtension.section_inverted v)

/-- Canonical coordinates for all 243 core elements, with the literal marked cubic line. -/
noncomputable def cubicInvertedCoordinates : (cubicOddCore c t.x) ≃
    (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) × cubicCoreLine c t.x :=
  t.cubicInvolutionExtension.coordinates.trans
    ((Equiv.refl _).prodCongr (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' _)).toEquiv)

@[simp] theorem cubicInvertedCoordinates_symm
    (v : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) (k : cubicCoreLine c t.x) :
    t.cubicInvertedCoordinates.symm (v,k)=t.cubicInvertedSection v*(k:cubicOddCore c t.x) := rfl

/-- The canonical cocycle is the previously constructed original commutator form. -/
theorem cubicInvertedSection_mul (v w : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    t.cubicInvertedSection (v*w)=t.cubicInvertedSection v*t.cubicInvertedSection w*
      (t.cubicCommutatorPairing v w:cubicOddCore c t.x) := by
  let := t.left_oddCore_quotient_elementary
  have h := t.cubicInvolutionExtension.section_mul v w
  change t.cubicInvertedSection (v*w)=t.cubicInvertedSection v*t.cubicInvertedSection w*
    (t.cubicInvolutionExtension.commutatorValue v w:cubicOddCore c t.x) at h
  rw [h]
  congr 1
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c t.x) v
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c t.x) w
  exact (t.cubicInvolutionExtension.commutatorValue_quotient v w).trans
    (t.cubicCommutatorPairing_mk v w).symm

omit [Finite G] in
/-- The actual Levi lies in the original involution centralizer. -/
theorem cubicLevi_le_H : t.leftCubicLevi≤c.H :=
  sup_le (map_subtype_le _) (zpowers_le.mpr t.n.property)

/-- The literal Levi action commutes with the original central involution. -/
theorem cubicLeviAction_commutes_involution (a : t.leftCubicLevi)
    (x : cubicOddCore c t.x) :
    t.cubicCoreAction (inclusion t.cubicLevi_le_normalizer a)
        (t.cubicInvolutionExtension.involution x)=
      t.cubicInvolutionExtension.involution
        (t.cubicCoreAction (inclusion t.cubicLevi_le_normalizer a) x) := by
  apply Subtype.ext
  change (a:G)*((t.z:G)*(x:G)*(t.z:G)⁻¹)*(a:G)⁻¹=
    (t.z:G)*((a:G)*(x:G)*(a:G)⁻¹)*(t.z:G)⁻¹
  have ha := mem_centralizer_singleton_iff.mp
    (t.centralizer ▸ t.cubicLevi_le_H a.property)
  calc
    _ = ((a:G)*(t.z:G))*(x:G)*((a:G)*(t.z:G))⁻¹ := by group
    _ = ((t.z:G)*(a:G))*(x:G)*((t.z:G)*(a:G))⁻¹ := by rw [ha]
    _ = _ := by group

/-- The whole Levi preserves the canonical inverted section. -/
theorem cubicInvertedSection_equivariant (a : t.leftCubicLevi)
    (v : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    t.cubicCoreAction (inclusion t.cubicLevi_le_normalizer a) (t.cubicInvertedSection v)=
      t.cubicInvertedSection (t.cubicAbelianizationAction
        (inclusion t.cubicLevi_le_normalizer a) v) :=
  t.cubicInvolutionExtension.section_equivariant _ _
    (t.cubicLeviAction_commutes_involution a) (fun _=>rfl) v

/-- The existing GL₂(3) coordinates act on the full section through the
original four-dimensional quotient action. -/
theorem cubicGLCoreAction_section (hc : Nat.card (cubicOddCore c t.x)=243)
    (a : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (v : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    t.cubicGLCoreAction hc a (t.cubicInvertedSection v)=
      t.cubicInvertedSection (t.cubicAbelianizationAction
        (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a)) v) :=
  t.cubicInvertedSection_equivariant ((t.cubicLeviLinearEquiv hc).symm a) v

/-- The reconstruction kernel is exactly the original derived line. -/
theorem cubicInvolutionExtension_kernel_derived
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    t.cubicInvolutionExtension.quotient.ker=_root_.commutator (cubicOddCore c t.x) := by
  change (QuotientGroup.mk' (cubicCoreLine c t.x)).ker=_
  rw [QuotientGroup.ker_mk',t.cubicCoreLine_eq_commutator hc]

/-- The original commutator pairing with its exact cubic-line codomain. -/
def cubicCommutatorLine (hc : Nat.card (cubicOddCore c t.x)=243)
    (v w : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) : cubicCoreLine c t.x :=
  ⟨t.cubicCommutatorPairing v w,t.cubicCommutatorPairing_line hc v w⟩

/-- The two literal descriptions of the cubic kernel agree. -/
def cubicExtensionKernelEquiv : t.cubicInvolutionExtension.quotient.ker ≃* cubicCoreLine c t.x :=
  MulEquiv.subgroupCongr (QuotientGroup.ker_mk' _)

theorem cubicExtensionPairing_eq (hc : Nat.card (cubicOddCore c t.x)=243)
    (v w : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    letI := t.left_oddCore_quotient_elementary
    t.cubicExtensionKernelEquiv (t.cubicInvolutionExtension.commutatorValue v w)=
      t.cubicCommutatorLine hc v w := by
  let := t.left_oddCore_quotient_elementary
  apply Subtype.ext
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c t.x) v
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c t.x) w
  exact (t.cubicInvolutionExtension.commutatorValue_quotient v w).trans
    (t.cubicCommutatorPairing_mk v w).symm

variable {D₂ V₂ : Type*} [Group D₂] [Group V₂] [IsMulCommutative V₂]
    (r : CubicInvolutionExtension D₂ V₂)

/-- Construct a full original core isomorphism from a quotient/line comparison
preserving the actual commutator. No full-core map is an input. -/
noncomputable def cubicCoreEquivOfForm (hc : Nat.card (cubicOddCore c t.x)=243)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* V₂)
    (f : cubicCoreLine c t.x ≃* r.quotient.ker)
    (hform : ∀ v w,f (t.cubicCommutatorLine hc v w)=r.commutatorValue (e v) (e w)) :
    cubicOddCore c t.x ≃* D₂ := by
  letI := t.left_oddCore_quotient_elementary
  apply t.cubicInvolutionExtension.liftEquiv r e (t.cubicExtensionKernelEquiv.trans f)
  intro v w
  change f (t.cubicExtensionKernelEquiv (t.cubicInvolutionExtension.commutatorValue v w))=_
  rw [t.cubicExtensionPairing_eq hc,hform]

/-- The reconstructed map has the prescribed literal quotient. -/
theorem cubicCoreEquivOfForm_quotient (hc : Nat.card (cubicOddCore c t.x)=243)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* V₂)
    (f : cubicCoreLine c t.x ≃* r.quotient.ker)
    (hform : ∀ v w,f (t.cubicCommutatorLine hc v w)=r.commutatorValue (e v) (e w))
    (x : cubicOddCore c t.x) :
    r.quotient (t.cubicCoreEquivOfForm r hc e f hform x)=
      e (QuotientGroup.mk' (cubicCoreLine c t.x) x) := by
  let := t.left_oddCore_quotient_elementary
  exact t.cubicInvolutionExtension.liftEquiv_quotient r e _ _ x

/-- The reconstructed map retains the prescribed original cubic-line map. -/
theorem cubicCoreEquivOfForm_line (hc : Nat.card (cubicOddCore c t.x)=243)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* V₂)
    (f : cubicCoreLine c t.x ≃* r.quotient.ker)
    (hform : ∀ v w,f (t.cubicCommutatorLine hc v w)=r.commutatorValue (e v) (e w))
    (x : cubicCoreLine c t.x) :
    t.cubicCoreEquivOfForm r hc e f hform x=(f x:D₂) := by
  let := t.left_oddCore_quotient_elementary
  exact t.cubicInvolutionExtension.liftEquiv_kernel r e _ _
    (t.cubicExtensionKernelEquiv.symm x)

/-- Quotient compatibility suffices for the full original GL₂(3) action.
The possible central discrepancy is removed by the proved derived-line equality. -/
theorem cubicCoreEquivOfForm_GL (hc : Nat.card (cubicOddCore c t.x)=243)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* V₂)
    (f : cubicCoreLine c t.x ≃* r.quotient.ker)
    (hform : ∀ v w,f (t.cubicCommutatorLine hc v w)=r.commutatorValue (e v) (e w))
    (a : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (a₂ : MulAut D₂) (b₂ : MulAut V₂)
    (ha₂ : ∀ x,a₂ (r.involution x)=r.involution (a₂ x))
    (hab₂ : ∀ x,r.quotient (a₂ x)=b₂ (r.quotient x))
    (he : ∀ v,e (t.cubicAbelianizationAction
        (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a)) v)=b₂ (e v))
    (x : cubicOddCore c t.x) :
    t.cubicCoreEquivOfForm r hc e f hform (t.cubicGLCoreAction hc a x)=
      a₂ (t.cubicCoreEquivOfForm r hc e f hform x) := by
  let := t.left_oddCore_quotient_elementary
  apply t.cubicInvolutionExtension.liftEquiv_equivariant_of_derived r
    (t.cubicInvolutionExtension_kernel_derived hc).le e _ _ (t.cubicGLCoreAction hc a) a₂
    (t.cubicAbelianizationAction
      (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a))) b₂
  · exact t.cubicLeviAction_commutes_involution _
  · exact ha₂
  · intro v
    rfl
  · exact hab₂
  · exact he

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
