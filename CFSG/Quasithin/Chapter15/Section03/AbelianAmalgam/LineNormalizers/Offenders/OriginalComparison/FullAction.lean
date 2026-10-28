module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.OriginalComparison

/-!
# The first-summand action of the full original Thompson subgroup

The Frattini decomposition I = I₀ C_I(V_E/E) makes I₀ surject onto
I's image in the original section quotient. Its exact first-summand kernel
therefore extends the representation uniquely to I. The two moved spaces
coincide, so the dimension calculation for I₀ gives the source calculation
for the full I.

`projection_conjugate` checks the mathematical action: on both coordinates
of the actual paired quotient, this extension agrees with ambient conjugation
by every original element of I. The correction acts trivially modulo E;
no equality between the original and temporary two-cores is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 15.3.67, printed pp.1153–1154, particularly the Frattini
comparison after dropping the temporary normalizer assumption.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.FullAction
open Replacement OriginalComparison Replacement.Transvections BestReduction.FullCoreTransfer
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  {Y T V M E Pc : Subgroup G} [IsMulCommutative V]
  (o : Geometry.OriginalData Y T V M E Pc)

variable [((Descent.sectionKernel V E).subgroupOf (lineNormalizer E)).Normal]

/-- The full original I mapped into the original section quotient. -/
noncomputable def sectionProjection (V E : Subgroup G)
    [((Descent.sectionKernel V E).subgroupOf (lineNormalizer E)).Normal] : lineI E →*
    ((lineNormalizer E) ⧸ (Descent.sectionKernel V E).subgroupOf (lineNormalizer E)) :=
  (QuotientGroup.mk' _).comp (inclusion (lineI_le_lineNormalizer E))

/-- The literal inclusion of the intrinsic I₀ in original I. -/
def inclusionI : originalActor T V E →* lineI E where
  toFun x := ⟨x.val.val, x.property.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- I₀ mapped to the same section-action image as I. -/
noncomputable def smallProjection (T V E : Subgroup G)
    [((Descent.sectionKernel V E).subgroupOf (lineNormalizer E)).Normal] : originalActor T V E →* (sectionProjection V E).range :=
  (sectionProjection V E).rangeRestrict.comp inclusionI

include o in
/-- Frattini correction preserves every original section-action image. -/
theorem smallProjection_surjective : Function.Surjective (smallProjection T V E) := by
  rintro ⟨z, i, rfl⟩
  have hi : i.val ∈ (lineI0 T V E : Set G) * (Descent.thompsonKernel V E : Set G) := by
    rw [← Descent.frattini_correction T V E o.line_le o.sylow o.sylow_image]
    exact i.property
  obtain ⟨j, hj, k, hk, he⟩ := hi
  let j₀ : originalActor T V E := ⟨⟨j,
    (show lineI0 T V E ≤ temporaryLineNormalizer T V E from
      (lineI0_eq_inf_temporary T V E).symm ▸ inf_le_right) hj⟩, hj⟩
  refine ⟨j₀, Subtype.ext ?_⟩
  change QuotientGroup.mk' ((Descent.sectionKernel V E).subgroupOf (lineNormalizer E))
    ⟨j, lineI_le_lineNormalizer E hj.1⟩ =
    QuotientGroup.mk' _ ((inclusion (lineI_le_lineNormalizer E)) i)
  apply (QuotientGroup.eq_iff_div_mem).mpr
  change j / i.val ∈ Descent.sectionKernel V E
  have hjL := lineI_le_lineNormalizer E hj.1
  have hkK : k ∈ Descent.sectionKernel V E := hk.2
  have hnorm := (normal_subgroupOf_iff_le_normalizer (Descent.sectionKernel_le V E)).mp
    (Descent.sectionKernel_normal V E o.line_le)
  rw [← he, div_eq_mul_inv, mul_inv_rev, ← mul_assoc]
  exact (hnorm hjL k⁻¹).mp ((Descent.sectionKernel V E).inv_mem hkK)

variable (σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) W)
  (hk : (σ.comp ((QuotientGroup.mk' (localCore T V E)).comp
    (localCentralizer T V E).subtype)).ker =
      ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
        (localCentralizer T V E))

include hk in
omit [Finite G] [IsMulCommutative V] in
private theorem lift_kernel : (smallProjection T V E).ker ≤ (originalRepresentation σ).asGroupHom.ker := by
  intro x hx
  have hx' : x.val.val ∈ Descent.sectionKernel V E := by
    have he := congrArg Subtype.val hx
    exact (QuotientGroup.eq_one_iff (inclusion (lineI_le_lineNormalizer E)
      (inclusionI x))).mp he
  apply Units.ext
  change x ∈ (originalRepresentation σ).ker
  rw [original_kernel σ hk]
  exact hx'

/-- The canonical extension through the actual section kernel. -/
noncomputable def representation : Representation (ZMod 2) (lineI E) W :=
  (Units.coeHom _).comp (((smallProjection T V E).liftOfSurjective (smallProjection_surjective o)
    ⟨(originalRepresentation σ).asGroupHom, by exact lift_kernel σ hk⟩).comp
      (sectionProjection V E).rangeRestrict)

/-- Restriction recovers the original I₀ action on the same first summand. -/
theorem representation_restrict (x : originalActor T V E) :
    representation o σ hk (inclusionI x) = originalRepresentation σ x := by
  unfold representation
  simp only [MonoidHom.comp_apply]
  change (Units.coeHom _) (((smallProjection T V E).liftOfSurjective
    (smallProjection_surjective o) ⟨_, lift_kernel σ hk⟩) (smallProjection T V E x)) = _
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

/-- Equal original section actions give equal first-summand actions. -/
theorem representation_eq_of_section_eq (i : lineI E) (j : originalActor T V E)
    (he : sectionProjection V E i = sectionProjection V E (inclusionI j)) :
    representation o σ hk i = originalRepresentation σ j := by
  rw [← representation_restrict o σ hk j]
  unfold representation
  simp only [MonoidHom.comp_apply]
  rw [show (sectionProjection V E).rangeRestrict i =
    (sectionProjection V E).rangeRestrict (inclusionI j) from Subtype.ext he]

/-- The source commutator for full I is exactly the moved space for I₀. -/
theorem moved_eq : Coinvariants.ker (representation o σ hk) =
    Coinvariants.ker (originalRepresentation σ) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, v⟩, rfl⟩
    obtain ⟨j, hj⟩ := smallProjection_surjective o ((sectionProjection V E).rangeRestrict i)
    change representation o σ hk i v - v ∈ _
    rw [representation_eq_of_section_eq o σ hk i j (congrArg Subtype.val hj).symm]
    exact Coinvariants.sub_mem_ker j v
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨j, v⟩, rfl⟩
    change originalRepresentation σ j v - v ∈ _
    rw [← representation_restrict o σ hk j]
    exact Coinvariants.sub_mem_ker (inclusionI j) v

/-- Ambient conjugation on the unchanged original span, expressed in H. -/
def conjugateVector (i : lineI E) (v : Additive (Replacement.Transvections.localSpan T V E)) :
    Additive (Replacement.Transvections.localSpan T V E) := by
  let w := i.val * v.toMul.val.val * i.val⁻¹
  have hw : w ∈ lineV V E :=
    (le_normalizer_conjugateSpanBy V (lineNormalizer E)
      (lineI_le_lineNormalizer E i.property) v.toMul.val.val).mp v.toMul.property
  exact Additive.ofMul ⟨⟨w, o.span_le_temporary hw⟩, hw⟩

section Projection
variable {L : Type*} [Group L]
  [(Replacement.Transvections.localSpan T V E).Normal] [IsElementaryAbelian 2 (Replacement.Transvections.localSpan T V E)]
  (f : temporaryLineNormalizer T V E →* L) (hf : Function.Surjective f)
  (hker : f.ker = centralizer (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E)))
  (ps : PairedSection (Replacement.Transvections.localSpan T V E) (localLine T V E)
    (localCentralizer T V E) (localCore T V E) f hf hker σ)

/-- The extended action is the actual action on both coordinates of U/E. -/
theorem projection_conjugate (i : lineI E) (v : Additive (Replacement.Transvections.localSpan T V E)) :
    ps.projection (conjugateVector o i v) =
      (representation o σ hk i (ps.projection v).1,
        representation o σ hk i (ps.projection v).2) := by
  obtain ⟨j, hj⟩ := smallProjection_surjective o ((sectionProjection V E).rangeRestrict i)
  have he : sectionProjection V E i = sectionProjection V E (inclusionI j) :=
    (congrArg Subtype.val hj).symm
  rw [representation_eq_of_section_eq o σ hk i j he]
  have hki : j.val.val⁻¹ * i.val ∈ Descent.sectionKernel V E := by
    change ((inclusion (lineI_le_lineNormalizer E) (inclusionI j))⁻¹ *
      inclusion (lineI_le_lineNormalizer E) i) ∈
        (Descent.sectionKernel V E).subgroupOf (lineNormalizer E)
    apply (QuotientGroup.eq_one_iff
      ((inclusion (lineI_le_lineNormalizer E) (inclusionI j))⁻¹ *
        inclusion (lineI_le_lineNormalizer E) i)).mp
    change (sectionProjection V E) (inclusionI j)⁻¹ * sectionProjection V E i = 1
    rw [map_inv, he, inv_mul_cancel]
  let vj := Representation.NormalElementaryQuotient.representation
    (Replacement.Transvections.localSpan T V E) f hf hker (f j.val) v
  have hp : ps.projection (conjugateVector o i v) = ps.projection vj := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (LinearMap.mem_ker).mp
    rw [ps.kernel_eq]
    change (i.val * v.toMul.val.val * i.val⁻¹) /
      (vj.toMul.val.val) ∈ E
    have hjv : vj.toMul.val.val = j.val.val * v.toMul.val.val * j.val.val⁻¹ :=
      congrArg Subtype.val (Representation.NormalElementaryQuotient.representation_apply
        (Replacement.Transvections.localSpan T V E) f hf hker j.val v)
    rw [hjv]
    have hc := ((Descent.mem_sectionKernel_iff V E
      (o.span_le_temporary.trans inf_le_left) _).mp hki).2
      v.toMul.val.val v.toMul.property
    have hc' : ⁅j.val.val⁻¹ * i.val, v.toMul.val.val⁆ ∈ E := by
      rw [← commutatorElement_inv]
      exact E.inv_mem hc
    have hjE := lineI_le_lineNormalizer E j.property.1
    have hex : i.val * v.toMul.val.val * i.val⁻¹ /
        (j.val.val * v.toMul.val.val * j.val.val⁻¹) =
        j.val.val * ⁅j.val.val⁻¹ * i.val, v.toMul.val.val⁆ * j.val.val⁻¹ := by
      simp only [commutatorElement_def, div_eq_mul_inv]
      group
    rw [hex]
    exact (hjE _).mp hc'
  rw [hp]
  exact ps.equivariant j.val (originalActor_le_centralizer j.property) v
end Projection

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.FullAction
