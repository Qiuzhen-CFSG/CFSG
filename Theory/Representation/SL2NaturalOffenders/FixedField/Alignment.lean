module
public import Theory.Representation.SL2NaturalOffenders.OuterSemilinear
public import Theory.Representation.SL2NaturalOffenders.FixedField.ActorAlignment

/-!
# Simultaneous field alignment on the natural SL₂ module

An outer involution on binary SL₂ is conjugate to a nontrivial field
involution. Use the same inner conjugator on the natural plane. Its remaining
additive intertwiner differs from the entrywise field action by a scalar,
since the additive commutant of natural SL₂ consists of field scalars. The
involution identity gives a norm-one scalar, removed by scalar Hilbert--90.
Thus a single field-linear change of coordinates aligns both actors. This is
the coherent marking required for fixed natural-module descent in
Aschbacher--Smith, Lemma 2.4.12(2), and the full-cover case of 2.4.23(1).
-/

public section
noncomputable section
namespace Representation.SL2NaturalOffenders.FixedField
open Matrix
variable {F : Type*} [Field F]

private def coefficientEquiv (σ : F ≃+* F) :
    (Fin 2 → F) ≃+ (Fin 2 → F) :=
  AddEquiv.piCongrRight (fun _ => σ.toAddEquiv)

private theorem coefficient_mulVec (σ : F ≃+* F)
    (g : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
    coefficientEquiv σ (g.val.mulVec v) =
      (Theory.PSL2.sl2FieldAut σ g).val.mulVec (coefficientEquiv σ v) := by
  ext i
  exact σ.toRingHom.map_mulVec g.val v i

private theorem coefficient_twice (σ : F ≃+* F) (hs : Function.Involutive σ)
    (v : Fin 2 → F) : coefficientEquiv σ (coefficientEquiv σ v) = v := by
  ext i
  exact hs _

variable [Algebra (ZMod 2) F]

private theorem scalar_of_field_intertwiner
    (σ : F ≃+* F) (hs : Function.Involutive σ)
    (e : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g v, e (g.val.mulVec v) =
      (Theory.PSL2.sl2FieldAut σ g).val.mulVec (e v)) :
    ∃ a : F, a ≠ 0 ∧ ∀ v, e v = a • coefficientEquiv σ v := by
  let f := e.toAddMonoidHom.comp (coefficientEquiv σ).toAddMonoidHom
  have hf : ∀ (g : SpecialLinearGroup (Fin 2) F) v, f (g.val.mulVec v) = g.val.mulVec (f v) := by
    intro g v
    change e (coefficientEquiv σ (g.val.mulVec v)) =
      g.val.mulVec (e (coefficientEquiv σ v))
    rw [coefficient_mulVec, he]
    have hg : Theory.PSL2.sl2FieldAut σ (Theory.PSL2.sl2FieldAut σ g) = g := by
      ext i j
      exact hs _
    rw [hg]
  obtain ⟨a, ha⟩ := centralizer_scalar f hf
  have hev (v) : e v = a • coefficientEquiv σ v := by
    have h := ha (coefficientEquiv σ v)
    change e (coefficientEquiv σ (coefficientEquiv σ v)) = _ at h
    rwa [coefficient_twice σ hs] at h
  refine ⟨a, ?_, hev⟩
  intro hz
  have h := hev (![(1:F),0])
  rw [hz, zero_smul] at h
  have hv := e.injective (h.trans e.map_zero.symm)
  have h0 := congrFun hv 0
  simp at h0

variable [CharP F 2]

omit [Algebra (ZMod 2) F] in
private theorem scalar_coboundary (σ : F ≃+* F) (a : F) (ha : a ≠ 0)
    (h : a * σ a = 1) : ∃ b : F, b ≠ 0 ∧ b * a = σ b := by
  by_cases h1 : a = 1
  · exact ⟨1, one_ne_zero, by simp [h1]⟩
  have hσ : σ a = a⁻¹ := (eq_inv_of_mul_eq_one_right h)
  refine ⟨1 + a⁻¹, ?_, ?_⟩
  · intro hz
    have hi : a⁻¹ = 1 := (CharTwo.add_eq_zero.mp hz).symm
    exact h1 (inv_eq_one.mp hi)
  · rw [map_add, map_one, map_inv₀, hσ, inv_inv]
    rw [add_mul, one_mul, inv_mul_cancel₀ ha, add_comm]

/-- Scalar Hilbert--90 removes the final natural-module ambiguity after the
actor has been aligned with a field involution. -/
private theorem field_intertwiner_scalar_alignment
    (σ : F ≃+* F) (hs : Function.Involutive σ)
    (e : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F)) (hi : Function.Involutive e)
    (he : ∀ g v, e (g.val.mulVec v) =
      (Theory.PSL2.sl2FieldAut σ g).val.mulVec (e v)) :
    ∃ b : F, b ≠ 0 ∧ ∀ v, b • e v = coefficientEquiv σ (b • v) := by
  obtain ⟨a, ha, hev⟩ := scalar_of_field_intertwiner σ hs e he
  have hnorm : a * σ a = 1 := by
    have h := hi (![(1:F),0])
    rw [hev, hev] at h
    have h0 := congrFun h 0
    simpa [coefficientEquiv, smul_eq_mul] using h0
  obtain ⟨b, hb, hba⟩ := scalar_coboundary σ a ha hnorm
  refine ⟨b, hb, fun v => ?_⟩
  rw [hev]
  ext i
  change b * (a * σ (v i)) = σ (b * v i)
  rw [← mul_assoc, hba, map_mul]

/-- Any specified inner alignment of the actor admits a compatible field-linear
alignment of its binary natural module. -/
theorem natural_alignment_of_actor
    (a : MulAut (SpecialLinearGroup (Fin 2) F))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F)) (hi : Function.Involutive E)
    (he : ∀ g v, E (g.val.mulVec v) = (a g).val.mulVec (E v))
    (σ : F ≃+* F) (hs : Function.Involutive σ)
    (c : SpecialLinearGroup (Fin 2) F)
    (hβ : ∀ g, (MulAut.conj c⁻¹) (a g) =
      Theory.PSL2.sl2FieldAut σ ((MulAut.conj c⁻¹) g)) :
    ∃ B : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F),
      (∀ g v, B (g.val.mulVec v) = ((MulAut.conj c⁻¹) g).val.mulVec (B v)) ∧
      (∀ v, B (E v) = fun i => σ (B v i)) := by
  let β := MulAut.conj c⁻¹
  let B₀ := SpecialLinearGroup.toLin' c⁻¹
  have hB₀ (g : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
      B₀ (g.val.mulVec v) = (β g).val.mulVec (B₀ v) := by
    change (SpecialLinearGroup.toLin' c⁻¹)
        (SpecialLinearGroup.toLin' g v) =
      (SpecialLinearGroup.toLin' (c⁻¹ * g * (c⁻¹)⁻¹)) (SpecialLinearGroup.toLin' c⁻¹ v)
    simp only [← LinearEquiv.mul_apply, ← map_mul]
    congr 2
    group
  have hB₀symm (g : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
      B₀.symm (g.val.mulVec v) = (β.symm g).val.mulVec (B₀.symm v) := by
    apply B₀.injective
    rw [B₀.apply_symm_apply, hB₀, B₀.apply_symm_apply, β.apply_symm_apply]
  let e := (B₀.restrictScalars (ZMod 2)).symm.trans
    (E.trans (B₀.restrictScalars (ZMod 2)))
  have hei : Function.Involutive e := by
    intro v
    change B₀ (E (B₀.symm (B₀ (E (B₀.symm v))))) = v
    rw [B₀.symm_apply_apply, hi, B₀.apply_symm_apply]
  have heσ (g : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
      e (g.val.mulVec v) = (Theory.PSL2.sl2FieldAut σ g).val.mulVec (e v) := by
    change B₀ (E (B₀.symm (g.val.mulVec v))) =
      (Theory.PSL2.sl2FieldAut σ g).val.mulVec (B₀ (E (B₀.symm v)))
    rw [hB₀symm, he, hB₀, hβ, β.apply_symm_apply]
  obtain ⟨b, hb, hbe⟩ := field_intertwiner_scalar_alignment σ hs e hei heσ
  let B := B₀.trans (LinearEquiv.smulOfNeZero F (Fin 2 → F) b hb)
  refine ⟨B, ?_, ?_⟩
  · intro g v
    change b • B₀ (g.val.mulVec v) = (β g).val.mulVec (b • B₀ v)
    rw [hB₀, Matrix.mulVec_smul]
  · intro v
    have h := hbe (B₀ v)
    change b • B₀ (E (B₀.symm (B₀ v))) = coefficientEquiv σ (b • B₀ v) at h
    rw [B₀.symm_apply_apply] at h
    exact h

variable [Finite F]

/-- An outer involution and its natural-module intertwiner are simultaneously
conjugate to one nontrivial field involution, with the same actor marking. -/
theorem outer_involution_natural_alignment
    (a : MulAut (SpecialLinearGroup (Fin 2) F))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F)) (hi : Function.Involutive E)
    (he : ∀ g v, E (g.val.mulVec v) = (a g).val.mulVec (E v))
    (ha : a ^ 2 = 1) (houter : ¬ ∃ g, a = MulAut.conj g) :
    ∃ σ : F ≃+* F, σ ≠ RingEquiv.refl F ∧ Function.Involutive σ ∧
      ∃ c : SpecialLinearGroup (Fin 2) F,
      ∃ B : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F),
        (∀ g v, B (g.val.mulVec v) = ((MulAut.conj c⁻¹) g).val.mulVec (B v)) ∧
        (∀ g, (MulAut.conj c⁻¹) (a g) =
          Theory.PSL2.sl2FieldAut σ ((MulAut.conj c⁻¹) g)) ∧
        (∀ v, B (E v) = fun i => σ (B v i)) := by
  obtain ⟨σ, hne, hs, c, hc⟩ := outer_involution_actor_alignment a ha houter
  obtain ⟨B, hB, hBE⟩ := natural_alignment_of_actor a E hi he σ hs c hc
  exact ⟨σ, hne, hs, c, B, hB, hc, hBE⟩
end Representation.SL2NaturalOffenders.FixedField
