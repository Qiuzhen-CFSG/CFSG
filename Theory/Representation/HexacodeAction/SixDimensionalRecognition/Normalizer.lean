module

public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.Coordinates
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.Normalizer.FiniteImage
public import Theory.Representation.HexacodeAction.EvenCommutant

/-!
# The exact binary normalizer of the even hexacode image

Conjugating the cubic scalar by a binary normalizer gives another element of
the binary commutant. The established commutant theorem therefore makes it
that scalar or its inverse. In the first case the normalizer respects the
actual four-element field structure and the checked field-linear normalizer
calculation applies. In the second case composing with the actual odd
involution reduces to the first case. Normality of the even subgroup gives
the reverse inclusion of the full hexacode image.

This proves the literal equality consumed as `hn` by
`SixDimensionalRecognition.exists_equivariant_of_finite_inputs`, so the even
intertwiner extends to the whole original group, including its odd coset.
Arbitrary-representation recognition and the source triple-cover comparison
remain separate from this concrete model calculation.

Source: Aschbacher–Smith, K.1.3, printed p.453 (PDF p.464), with the terminal
application on printed p.1155 (PDF p.1172). The existing ATLAS carriers and
licensed ports are unchanged. Certificate reconstruction and measurements
are recorded in `Normalizer/source/README.md`.
-/

@[expose] public section

open Atlas.Codes Subgroup
namespace Representation.Hexacode.SixDimensional
open EvenImage
private noncomputable def forgetField : FieldGL →* BinaryGL where
  toFun v := v.restrictScalars Bit
  map_one' := rfl
  map_mul' _ _ := rfl
private theorem forgetField_injective : Function.Injective forgetField := by
  intro v w h
  apply LinearEquiv.ext
  intro x
  exact LinearEquiv.congr_fun h x
private theorem forgetField_even (g : HexEvenAutomorphisms) :
    forgetField (evenFieldAction g) = hexAction g.val := rfl
private theorem evenBinaryImage_eq_map : evenBinaryImage = hexSign.ker.map hexAction := by
  rw [evenBinaryImage, MonoidHom.range_comp, Subgroup.range_subtype]
private theorem full_le_normalizer : hexAction.range ≤
    Subgroup.normalizer (evenBinaryImage : Set BinaryGL) := by
  rw [evenBinaryImage_eq_map]
  rintro _ ⟨g, rfl⟩
  apply Subgroup.le_normalizer_map hexAction
  exact ⟨g, by rw [hexSign.ker.normalizer_eq_top]; trivial, rfl⟩

private theorem conjugates_scalar (x : BinaryGL)
    (hx : x ∈ Subgroup.normalizer (evenBinaryImage : Set BinaryGL)) :
    MulAut.conj x (hexAction hexZ) = hexAction hexZ ∨
    MulAut.conj x (hexAction hexZ) = (hexAction hexZ)⁻¹ := by
  have hc : ∀ (g : HexEvenAutomorphisms) w,
      (MulAut.conj x (hexAction hexZ)) (action g.val w) =
      action g.val ((MulAut.conj x (hexAction hexZ)) w) := by
    intro g w
    have hm : x⁻¹ * hexAction g.val * x ∈ evenBinaryImage := by
      have hi := (Subgroup.normalizer (evenBinaryImage : Set BinaryGL)).inv_mem hx
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hi (hexAction g.val)).mp
        (show hexAction g.val ∈ evenBinaryImage from ⟨g, rfl⟩)
    obtain ⟨j,hj⟩ := hm
    change hexAction j.val = x⁻¹ * hexAction g.val * x at hj
    have hzj : Commute (hexAction hexZ) (hexAction j.val) := by
      apply LinearEquiv.ext
      intro u
      exact (action_commutes_scalar j.val j.property u).symm
    have he := hzj.map (MulAut.conj x).toMonoidHom
    have hjx : MulAut.conj x (hexAction j.val) = hexAction g.val := by
      rw [hj]
      simp [MulAut.conj_apply, mul_assoc]
    change Commute (MulAut.conj x (hexAction hexZ)) (MulAut.conj x (hexAction j.val)) at he
    rw [hjx] at he
    exact LinearEquiv.congr_fun he.eq w
  obtain ⟨k,hk⟩ := commuting_even_automorphism_eq_scalar (MulAut.conj x (hexAction hexZ)) hc
  have he : MulAut.conj x (hexAction hexZ) = hexAction (hexZ ^ k.val) :=
    LinearEquiv.ext hk
  fin_cases k
  · have hz : hexAction hexZ = 1 := by
      apply (MulAut.conj x).injective
      simpa only [Fin.val_zero, pow_zero, map_one] using he
    exact (hexZ_ne_one (hexAction_injective (hz.trans hexAction.map_one.symm))).elim
  · left
    simpa only [Fin.val_one, pow_one] using he
  · right
    have hi : hexZ ^ 2 = hexZ⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      simpa only [← pow_succ] using hexZ_cube
    change MulAut.conj x (hexAction hexZ) = hexAction (hexZ ^ 2) at he
    simpa only [hi, map_inv] using he

private noncomputable def fieldLinear (x : BinaryGL)
    (hx : MulAut.conj x (hexAction hexZ) = hexAction hexZ) : FieldGL :=
  { x with
    map_smul' r w := by
      change x (r • w) = r • x w
      have hc : x * hexAction hexZ = hexAction hexZ * x :=
        mul_inv_eq_iff_eq_mul.mp hx
      have hh := LinearEquiv.congr_fun hc w
      change x (action hexZ w) = action hexZ (x w) at hh
      rw [field_smul_formula, map_add, map_smul, map_smul, hh, ← field_smul_formula]
  }

private theorem linear_normalizer_mem (x : BinaryGL)
    (hx : x ∈ Subgroup.normalizer (evenBinaryImage : Set BinaryGL))
    (hz : MulAut.conj x (hexAction hexZ) = hexAction hexZ) : x ∈ hexAction.range := by
  let v := fieldLinear x hz
  have hf : forgetField v = x := rfl
  have hm (g : HexEvenAutomorphisms) : v * evenFieldAction g * v⁻¹ ∈ evenFieldAction.range := by
    have he : x * hexAction g.val * x⁻¹ ∈ evenBinaryImage :=
      (Subgroup.mem_normalizer_iff.mp hx _).mp ⟨g, rfl⟩
    obtain ⟨a,ha⟩ := he
    change hexAction a.val = x * hexAction g.val * x⁻¹ at ha
    refine ⟨a, forgetField_injective ?_⟩
    simpa only [map_mul, map_inv, forgetField_even, hf] using ha
  obtain ⟨g,hg⟩ := mem_evenFieldAction_of_conjugating_generators v (hm generatorA) (hm generatorB)
  exact ⟨g.val, congrArg forgetField hg⟩

/-- The exact binary normalizer of the actual even hexacode image is the full image. -/
theorem normalizer_evenBinaryImage :
    Subgroup.normalizer (evenBinaryImage : Set BinaryGL) = hexAction.range := by
  apply le_antisymm _ full_le_normalizer
  intro x hx
  rcases conjugates_scalar x hx with hz | hz
  · exact linear_normalizer_mem x hx hz
  · let t := hexAction fieldInvolution
    have ht : t ∈ hexAction.range := ⟨fieldInvolution, rfl⟩
    have hti : MulAut.conj t (hexAction hexZ) = (hexAction hexZ)⁻¹ := by
      change hexAction fieldInvolution * hexAction hexZ * (hexAction fieldInvolution)⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul, hex_conjugation_odd _ fieldInvolution_odd, map_inv]
    have hxt : MulAut.conj (x * t) (hexAction hexZ) = hexAction hexZ := by
      rw [map_mul]
      change MulAut.conj x (MulAut.conj t (hexAction hexZ)) = _
      rw [hti, map_inv, hz, inv_inv]
    have hh := linear_normalizer_mem (x*t)
      ((Subgroup.normalizer (evenBinaryImage : Set BinaryGL)).mul_mem hx (full_le_normalizer ht)) hxt
    have hm := hexAction.range.mul_mem hh (hexAction.range.inv_mem ht)
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using hm
end Representation.Hexacode.SixDimensional
