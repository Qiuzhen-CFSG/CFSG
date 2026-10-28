module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M22.OuterActions
public import Theory.Representation.BinaryAbsoluteExtension


/-!
# Whole ambient actions on the M₂₂ code and cocode

Absolute irreducibility over F₂ forces the chosen component intertwiner to
intertwine the whole group. The actual conjugation embedding in the setwise
pair stabilizer retains its marking on L; its image is the native M₂₂ or the
whole pair stabilizer. The two literal quotient modules remain distinct.

Source: Aschbacher–Smith H.13.1–2, printed p.395, and K.4, printed p.457.
The general scalar-rigidity argument is in `BinaryAbsoluteExtension`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Representation Sporadic.Mathieu MathieuCode
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source
noncomputable section
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

private theorem simple_pair_index : m22ToPairStabilizer.range.index = 2 := by
  have hi : Function.Injective m22ToPairStabilizer :=
    fun _ _ he => m22Embedding_injective (congrArg Subtype.val he)
  have hc : Nat.card m22ToPairStabilizer.range = 443520 :=
    (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv.symm).trans m22_order
  have hh := m22ToPairStabilizer.range.card_mul_index
  rw [hc, MathieuCode.m22PairStabilizer_card] at hh
  omega

omit [Finite G] in
/-- The component maps onto the literal native M₂₂ subgroup. -/
theorem simpleAmbientPairHom_component_image (e : L ≃* M22) (hN : L.Normal) :
    L.map (simpleAmbientPairHom L e hN) = m22ToPairStabilizer.range := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨e ⟨y, hy⟩, (simpleAmbientPairHom_on_component e hN ⟨y, hy⟩).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := e.surjective y
    exact ⟨z, z.property, simpleAmbientPairHom_on_component e hN z⟩

omit [Finite G] in
/-- The actual ambient image is inner or the full pair stabilizer. -/
theorem simpleAmbientPairHom_range_cases (e : L ≃* M22) (hN : L.Normal) :
    (simpleAmbientPairHom L e hN).range = m22ToPairStabilizer.range ∨
      (simpleAmbientPairHom L e hN).range = ⊤ := by
  let R := (simpleAmbientPairHom L e hN).range
  have hle : m22ToPairStabilizer.range ≤ R := by
    rw [← simpleAmbientPairHom_component_image e hN]
    exact Subgroup.map_le_range (simpleAmbientPairHom L e hN) L
  by_cases he : R = m22ToPairStabilizer.range
  · exact Or.inl he
  right
  apply top_unique
  have hn : ¬ R ≤ m22ToPairStabilizer.range := fun hh => he (le_antisymm hh hle)
  obtain ⟨a, haR, ha⟩ := SetLike.not_le_iff_exists.mp hn
  intro x _
  by_cases hx : x ∈ m22ToPairStabilizer.range
  · exact hle hx
  have hxa : x * a⁻¹ ∈ m22ToPairStabilizer.range :=
    (Subgroup.mul_mem_iff_of_index_two simple_pair_index).mpr
      (iff_of_false hx (fun hh => ha (m22ToPairStabilizer.range.inv_mem hh)))
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using R.mul_mem (hle hxa) haR

/-- Extend the given code intertwiner without changing its linear map. -/
def sourceCodeAmbientEquiv (h : SourceHypotheses ρ L) (e : L ≃* M22)
    (E : Equiv (ρ.comp L.subtype) (m22CodeRepresentation.comp e.toMonoidHom)) :
    Equiv ρ (simpleCodeAmbientRepresentation L e (by rw [h.component]; infer_instance)) := by
  let hN : L.Normal := by rw [h.component]; infer_instance
  let := hN
  let τ := simpleCodeAmbientRepresentation L e hN
  have hres : τ.comp L.subtype = m22CodeRepresentation.comp e.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply LinearMap.ext
    intro v
    exact simpleCodeAmbientRepresentation_on_component e hN x v
  have ha : IsAbsolutelyIrreducible (τ.comp L.subtype) := by
    rw [hres]
    exact binary_absolute_comp_surjective _ e.toMonoidHom e.surjective
      m22Code_isAbsolutelyIrreducible
  let E₀ : Equiv (ρ.comp L.subtype) (τ.comp L.subtype) :=
    Representation.Equiv.mk E.toLinearEquiv (fun x => LinearMap.ext
      (simpleAmbientPairHom_code_intertwining h e hN E x))
  exact Representation.Equiv.mk E.toLinearEquiv (fun g => LinearMap.ext
    (binary_extension_intertwining ρ τ L ha E₀ g))

/-- Extend the given cocode intertwiner without changing its linear map. -/
def sourceCocodeAmbientEquiv (h : SourceHypotheses ρ L) (e : L ≃* M22)
    (E : Equiv (ρ.comp L.subtype) (m22CocodeRepresentation.comp e.toMonoidHom)) :
    Equiv ρ (simpleCocodeAmbientRepresentation L e (by rw [h.component]; infer_instance)) := by
  let hN : L.Normal := by rw [h.component]; infer_instance
  let := hN
  let τ := simpleCocodeAmbientRepresentation L e hN
  have hres : τ.comp L.subtype = m22CocodeRepresentation.comp e.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply LinearMap.ext
    intro v
    exact simpleCocodeAmbientRepresentation_on_component e hN x v
  have ha : IsAbsolutelyIrreducible (τ.comp L.subtype) := by
    rw [hres]
    exact binary_absolute_comp_surjective _ e.toMonoidHom e.surjective
      m22Cocode_isAbsolutelyIrreducible
  let E₀ : Equiv (ρ.comp L.subtype) (τ.comp L.subtype) :=
    Representation.Equiv.mk E.toLinearEquiv (fun x => LinearMap.ext
      (simpleAmbientPairHom_cocode_intertwining h e hN E x))
  exact Representation.Equiv.mk E.toLinearEquiv (fun g => LinearMap.ext
    (binary_extension_intertwining ρ τ L ha E₀ g))

theorem sourceCodeAmbientEquiv_apply (h : SourceHypotheses ρ L) (e : L ≃* M22)
    (E : Equiv (ρ.comp L.subtype) (m22CodeRepresentation.comp e.toMonoidHom)) (v : V) :
    sourceCodeAmbientEquiv h e E v = E v := rfl

theorem sourceCocodeAmbientEquiv_apply (h : SourceHypotheses ρ L) (e : L ≃* M22)
    (E : Equiv (ρ.comp L.subtype) (m22CocodeRepresentation.comp e.toMonoidHom)) (v : V) :
    sourceCocodeAmbientEquiv h e E v = E v := rfl

end
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source
