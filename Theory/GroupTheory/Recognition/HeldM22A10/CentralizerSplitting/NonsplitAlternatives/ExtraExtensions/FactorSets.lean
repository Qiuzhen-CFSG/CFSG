module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.Actions
public import Mathlib.GroupTheory.GroupExtension.Basic
public import Mathlib.GroupTheory.Complement

/-!
# Factor sets for the binary Held extensions

A normalized factor set records the multiplication of chosen lifts of S4.
An action extension is a genuine short exact sequence with the specified
conjugation action. Choosing a normalized section gives a factor set and
unique coordinates for every element. A coboundary produces a complement to
the exact image of the inclusion; cohomologous factor sets produce an actual
multiplicative equivalence between the extension groups.

These elementary extension arguments reduce the two additional action cases
in Huppert--Blackburn, *Finite Groups III*, XII.1.18(b), p.314, to finite
cocycle calculations. No vanishing or completeness calculation is assumed to
be proved here.
-/

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions
open LocalModelDichotomy
universe u v

/-- A normalized multiplicative two-cocycle for the given binary action. -/
public structure FactorSet (α : SymmetricFour →* MulAut BinaryFour) where
  value : SymmetricFour → SymmetricFour → BinaryFour
  one_left : ∀ s, value 1 s = 1
  one_right : ∀ s, value s 1 = 1
  cocycle : ∀ s t r, value s t * value (s * t) r =
    α s (value t r) * value s (t * r)

namespace FactorSet
variable {α : SymmetricFour →* MulAut BinaryFour}

/-- The factor set of the split extension. -/
@[expose] public def trivial (α : SymmetricFour →* MulAut BinaryFour) : FactorSet α where
  value _ _ := 1
  one_left _ := rfl
  one_right _ := rfl
  cocycle _ _ _ := by simp

/-- The precise change-of-section equation, with a normalized correcting cochain. -/
@[expose] public def Cohomologous (c d : FactorSet α) : Prop :=
  ∃ b : SymmetricFour → BinaryFour, b 1 = 1 ∧
    ∀ s t, c.value s t * b (s * t) = b s * α s (b t) * d.value s t

/-- A coboundary is cohomologous to the trivial factor set. -/
@[expose] public def IsCoboundary (c : FactorSet α) : Prop :=
  c.Cohomologous (trivial α)

end FactorSet

/-- A short exact sequence with its actual prescribed conjugation action. -/
public structure ActionExtension (α : SymmetricFour →* MulAut BinaryFour)
    (H : Type u) [Group H] extends GroupExtension BinaryFour H SymmetricFour where
  conjugation : ∀ h w, inl (α (rightHom h) w) = h * inl w * h⁻¹

namespace ActionExtension
variable {α : SymmetricFour →* MulAut BinaryFour} {H : Type u} [Group H]
variable (E : ActionExtension α H)

/-- A section normalized at the identity; it is not presumed multiplicative. -/
@[expose] public noncomputable def normalizedSection (s : SymmetricFour) : H :=
  if s = 1 then 1 else Function.surjInv E.rightHom_surjective s

@[simp] public theorem section_one : E.normalizedSection 1 = 1 := by simp [normalizedSection]

@[simp] public theorem projection_section (s : SymmetricFour) :
    E.rightHom (E.normalizedSection s) = s := by
  classical
  by_cases hs : s = 1
  · simp [normalizedSection, hs]
  · simp [normalizedSection, hs, Function.surjInv_eq]

/-- Recover the binary coordinate of an element of the exact kernel. -/
@[expose] public noncomputable def kernelValue (h : H) (hh : E.rightHom h = 1) : BinaryFour :=
  (MonoidHom.ofInjective E.inl_injective).symm
    ⟨h, by rw [E.range_inl_eq_ker_rightHom]; exact hh⟩

@[simp] public theorem inl_kernelValue (h : H) (hh : E.rightHom h = 1) :
    E.inl (E.kernelValue h hh) = h :=
  MonoidHom.apply_ofInjective_symm E.inl_injective _

/-- The binary coordinate of the defect in multiplication of two lifts. -/
@[expose] public noncomputable def factorValue (s t : SymmetricFour) : BinaryFour :=
  E.kernelValue (E.normalizedSection s * E.normalizedSection t * (E.normalizedSection (s * t))⁻¹)
    (by simp only [map_mul, map_inv, projection_section, mul_inv_cancel])

@[simp] public theorem inl_factorValue (s t : SymmetricFour) :
    E.inl (E.factorValue s t) =
      E.normalizedSection s * E.normalizedSection t * (E.normalizedSection (s * t))⁻¹ :=
  E.inl_kernelValue _ _

/-- Associativity of the extension gives the normalized cocycle equations. -/
@[expose] public noncomputable def factorSet : FactorSet α where
  value := E.factorValue
  one_left s := by
    apply E.inl_injective
    simp
  one_right s := by
    apply E.inl_injective
    simp
  cocycle s t r := by
    apply E.inl_injective
    simp only [map_mul, inl_factorValue]
    rw [← E.projection_section s, E.conjugation, E.projection_section s,
      E.inl_factorValue]
    simp only [mul_assoc]
    group

/-- Unique binary and quotient coordinates for the actual extension group. -/
@[expose] public noncomputable def normalForm : BinaryFour × SymmetricFour ≃ H where
  toFun p := E.inl p.1 * E.normalizedSection p.2
  invFun h := (E.kernelValue (h * (E.normalizedSection (E.rightHom h))⁻¹)
    (by simp only [map_mul, map_inv, projection_section, mul_inv_cancel]), E.rightHom h)
  left_inv p := by
    rcases p with ⟨w, s⟩
    apply Prod.ext
    · apply E.inl_injective
      simp only [map_mul, E.rightHom_inl, projection_section, one_mul,
        inl_kernelValue, mul_inv_cancel_right]
    · simp only [map_mul, E.rightHom_inl, projection_section, one_mul]
  right_inv h := by
    simp only [inl_kernelValue, inv_mul_cancel_right]

public theorem normalForm_apply (w : BinaryFour) (s : SymmetricFour) :
    E.normalForm (w, s) = E.inl w * E.normalizedSection s := rfl

/-- The multiplication law of the actual group in these coordinates. -/
public theorem normalForm_mul (w x : BinaryFour) (s t : SymmetricFour) :
    E.normalForm (w * α s x * E.factorSet.value s t, s * t) =
      E.normalForm (w, s) * E.normalForm (x, t) := by
  simp only [normalForm_apply, map_mul]
  change E.inl w * E.inl (α s x) * E.inl (E.factorValue s t) * E.normalizedSection (s * t) = _
  rw [← E.projection_section s, E.conjugation, E.projection_section s, E.inl_factorValue]
  group

/-- A homomorphic section complements the exact inclusion image. -/
public theorem complement_of_section (σ : SymmetricFour →* H)
    (hσ : ∀ s, E.rightHom (σ s) = s) : E.inl.range.IsComplement' σ.range := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · apply Subgroup.disjoint_def.mpr
    intro h hi hσh
    obtain ⟨s, rfl⟩ := hσh
    have hs : s = 1 := by
      rw [E.range_inl_eq_ker_rightHom] at hi
      exact (hσ s).symm.trans hi
    simp [hs]
  · apply Set.eq_univ_iff_forall.mpr
    intro h
    refine ⟨h * (σ (E.rightHom h))⁻¹, ?_, σ (E.rightHom h), ⟨_, rfl⟩, ?_⟩
    · rw [E.range_inl_eq_ker_rightHom]
      change E.rightHom (h * (σ (E.rightHom h))⁻¹) = 1
      rw [map_mul, map_inv, hσ, mul_inv_cancel]
    · exact inv_mul_cancel_right _ _

/-- Correct a coboundary section to obtain a complement of the specified kernel. -/
public theorem complement_of_isCoboundary (hc : E.factorSet.IsCoboundary) :
    ∃ K : Subgroup H, E.inl.range.IsComplement' K := by
  obtain ⟨b, hb, hbc⟩ := hc
  let σ : SymmetricFour →* H :=
    { toFun := fun s => E.normalForm ((b s)⁻¹, s)
      map_one' := by simp [normalForm_apply, hb]
      map_mul' := by
        intro s t
        rw [← E.normalForm_mul]
        apply congrArg E.normalForm
        refine Prod.ext ?_ rfl
        have hcst : E.factorSet.value s t = b s * α s (b t) * (b (s * t))⁻¹ := by
          apply eq_mul_inv_iff_mul_eq.mpr
          simpa only [FactorSet.trivial, mul_one] using hbc s t
        simp only [map_inv, hcst]
        simp [mul_assoc, mul_left_comm, mul_comm] }
  refine ⟨σ.range, E.complement_of_section σ ?_⟩
  intro s
  change E.rightHom (E.inl ((b s)⁻¹) * E.normalizedSection s) = s
  rw [map_mul, E.rightHom_inl, E.projection_section, one_mul]

private def shift (b : SymmetricFour → BinaryFour) :
    BinaryFour × SymmetricFour ≃ BinaryFour × SymmetricFour where
  toFun p := (p.1 * b p.2, p.2)
  invFun p := (p.1 * (b p.2)⁻¹, p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- An explicit correcting cochain gives an equivalence of the extension groups. -/
public noncomputable def equivOfCorrection {H' : Type v} [Group H']
    (E' : ActionExtension α H') (b : SymmetricFour → BinaryFour)
    (hbc : ∀ s t, E.factorSet.value s t * b (s * t) =
      b s * α s (b t) * E'.factorSet.value s t) : H ≃* H' := by
  refine { (E.normalForm.symm.trans (shift b)).trans E'.normalForm with map_mul' := ?_ }
  intro h k
  obtain ⟨⟨w, s⟩, rfl⟩ := E.normalForm.surjective h
  obtain ⟨⟨x, t⟩, rfl⟩ := E.normalForm.surjective k
  change E'.normalForm (shift b (E.normalForm.symm
    (E.normalForm (w, s) * E.normalForm (x, t)))) =
      E'.normalForm (shift b (E.normalForm.symm (E.normalForm (w, s)))) *
        E'.normalForm (shift b (E.normalForm.symm (E.normalForm (x, t))))
  rw [← E.normalForm_mul]
  simp only [Equiv.symm_apply_apply]
  change E'.normalForm ((w * α s x * E.factorSet.value s t) * b (s * t), s * t) =
    E'.normalForm (w * b s, s) * E'.normalForm (x * b t, t)
  rw [← E'.normalForm_mul]
  apply congrArg E'.normalForm
  refine Prod.ext ?_ rfl
  change w * α s x * E.factorSet.value s t * b (s * t) =
    w * b s * α s (x * b t) * E'.factorSet.value s t
  rw [mul_assoc (w * α s x), hbc s t, map_mul]
  simp only [mul_assoc, mul_left_comm, mul_comm]

/-- Cohomologous factor sets give an actual equivalence of the extension groups. -/
public noncomputable def equivOfCohomologous {H' : Type v} [Group H']
    (E' : ActionExtension α H') (hc : E.factorSet.Cohomologous E'.factorSet) : H ≃* H' :=
  E.equivOfCorrection E' (Classical.choose hc) (Classical.choose_spec hc).2

end ActionExtension
end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions
