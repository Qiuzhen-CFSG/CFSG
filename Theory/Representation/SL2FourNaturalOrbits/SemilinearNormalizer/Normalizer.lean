module

public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.Labels
public import Theory.Representation.SL2NaturalOffenders.Semilinear

/-!
# The exact binary normalizer of natural SL₂(4)

The determinant-label kernel gives the forward inclusion. For the reverse
inclusion, the existing natural-SL₂ scalar-commutant theorem supplies the field
automorphism of every binary normalizer element. Removing that automorphism
gives an invertible field-linear map. Thus the original faithful action yields
an actual multiplicative equivalence ΓL₂(4) ≃ N_GL₄(2)(SL₂(4)).

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of 6.2.5,
printed p.681 (PDF p.698).
-/

@[expose] public section
noncomputable section
namespace Representation.SL2FourNatural.SemilinearNormalizer
open Matrix
open Matrix.GeneralLinearGroup
/-- The normalizer acts semilinearly for the original F₄-vector-space structure. -/
theorem normalizer_has_coefficients (x : BinaryGL) (hx : x ∈ normalizer) :
    ∃ σ : F ≃+* F, ∀ (c : F) (v : V), x (c • v) = σ c • x v := by
  let L := action.range.subgroupOf normalizer
  have : L.Normal := Subgroup.normal_in_normalizer (H := action.range)
  let e : L ≃* SL :=
    (Subgroup.subgroupOfEquivOfLe action.range.le_normalizer).trans
      (MonoidHom.ofInjective action_faithful).symm
  let ρ : Representation (ZMod 2) normalizer V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp normalizer.subtype
  have hnat (g : L) (v : V) : ρ (g : normalizer) v = (e g).val.mulVec v := by
    have he : action (e g) = g.val.val :=
      MonoidHom.apply_ofInjective_symm action_faithful _
    change g.val.val v = action (e g) v
    rw [he]
  exact SL2NaturalOffenders.normalizer_semilinear L e ρ hnat ⟨x, hx⟩

theorem normalizer_le_semilinear : normalizer ≤ semilinear := by
  intro x hx
  obtain ⟨σ, hσ⟩ := normalizer_has_coefficients x hx
  exact natural_exists x σ hσ

/-- Each semilinear actor normalizes the actual determinant-one image. -/
theorem semilinear_le_normalizer : semilinear ≤ normalizer := by
  rw [normalizer, Subgroup.le_normalizer_iff]
  rintro _ ⟨g, rfl⟩ _ ⟨A, rfl⟩
  have hn : special.range.Normal := labels_ker ▸ inferInstance
  have hm : g * special A * g⁻¹ ∈ special.range :=
    hn.conj_mem _ ⟨A, rfl⟩ g
  obtain ⟨B, hB⟩ := hm
  refine ⟨B, ?_⟩
  have he := congrArg natural hB
  simpa only [map_mul, map_inv, natural_special] using he

/-- The full binary-linear normalizer of SL₂(4) is the faithful ΓL₂(4) image. -/
theorem semilinear_eq_normalizer : semilinear = normalizer :=
  le_antisymm semilinear_le_normalizer normalizer_le_semilinear

/-- Actual group identification, retaining the natural action as the inclusion. -/
def normalizerEquiv : Gamma ≃* normalizer :=
  (MonoidHom.ofInjective natural_injective).trans
    (MulEquiv.subgroupCongr semilinear_eq_normalizer)

theorem normalizerEquiv_apply (g : Gamma) : (normalizerEquiv g : BinaryGL) = natural g := rfl

/-- Every normalizer element is either field-linear or field-linear after Frobenius. -/
theorem normalizer_cases (x : BinaryGL) (hx : x ∈ normalizer) :
    ∃ A : LinearGroup, x = linear A ∨ x = linear A * frobeniusLinear := by
  obtain ⟨g, rfl⟩ := normalizer_le_semilinear hx
  refine ⟨g.left, ?_⟩
  rcases fieldAutomorphism_cases g.right with h | h
  · left
    apply LinearEquiv.ext
    intro v
    change glEquiv g.left (fun i => g.right (v i)) = glEquiv g.left v
    rw [h]
    rfl
  · right
    apply LinearEquiv.ext
    intro v
    change glEquiv g.left (fun i => g.right (v i)) = glEquiv g.left (frobeniusLinear v)
    rw [h]
    rfl

/-- The label action of the literal binary-linear normalizer. -/
def normalizerLabels : normalizer →* Equiv.Perm Fˣ :=
  labels.comp normalizerEquiv.symm.toMonoidHom

@[simp] theorem normalizerLabels_equiv (g : Gamma) :
    normalizerLabels (normalizerEquiv g) = labels g := by
  simp [normalizerLabels]

theorem normalizerLabels_surjective : Function.Surjective normalizerLabels := by
  intro p
  obtain ⟨g, rfl⟩ := labels_surjective p
  exact ⟨normalizerEquiv g, normalizerLabels_equiv g⟩

/-- The label kernel inside the normalizer is exactly the original SL₂ image. -/
theorem normalizerLabels_ker : normalizerLabels.ker = action.range.subgroupOf normalizer := by
  ext x
  obtain ⟨g, rfl⟩ := normalizerEquiv.surjective x
  change normalizerLabels (normalizerEquiv g) = 1 ↔ natural g ∈ action.range
  rw [normalizerLabels_equiv, ← MonoidHom.mem_ker, labels_ker]
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A, (natural_special A).symm⟩
  · rintro ⟨A, hA⟩
    exact ⟨A, natural_injective ((natural_special A).trans hA)⟩

instance normalizer_special_normal : (action.range.subgroupOf normalizer).Normal :=
  Subgroup.normal_in_normalizer (H := action.range)

/-- Actual symmetric-group identification for the source normalizer quotient. -/
def normalizerQuotientEquiv :
    normalizer ⧸ (action.range.subgroupOf normalizer) ≃* Equiv.Perm (Fin 3) := by
  have : (action.range.subgroupOf normalizer).Normal :=
    Subgroup.normal_in_normalizer (H := action.range)
  exact (QuotientGroup.quotientMulEquivOfEq normalizerLabels_ker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective normalizerLabels normalizerLabels_surjective).trans
      (Equiv.permCongrHom (Fintype.equivFinOfCardEq card_labels)))

/-- The two marked SL₂–Frobenius subgroups are identified by the natural action. -/
def specialFieldEquiv : specialFieldGamma ≃* specialField :=
  (specialFieldGamma.equivMapOfInjective natural natural_injective).trans
    (MulEquiv.subgroupCongr specialFieldGamma_map_natural)

theorem specialFieldEquiv_apply (g : specialFieldGamma) :
    (specialFieldEquiv g : BinaryGL) = natural g.val := rfl

/-- The label permutation of the literal generated binary subgroup. -/
def specialFieldLabels : specialField →* Equiv.Perm Fˣ :=
  (labels.comp specialFieldGamma.subtype).comp specialFieldEquiv.symm.toMonoidHom

/-- The orbit calculation is valid for the original binary actors. -/
theorem specialField_label_orbit (a b : Fˣ) :
    (∃ g : specialField, specialFieldLabels g a = b) ↔ (a = 1 ↔ b = 1) := by
  rw [← specialFieldGamma_label_orbit]
  constructor
  · rintro ⟨g, h⟩
    exact ⟨specialFieldEquiv.symm g, h⟩
  · rintro ⟨g, h⟩
    refine ⟨specialFieldEquiv g, ?_⟩
    simpa [specialFieldLabels] using h

end Representation.SL2FourNatural.SemilinearNormalizer
