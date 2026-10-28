module
public import Theory.Representation.BinaryNormalizerResidual
public import Theory.Representation.BinaryOffender.CubicRatio

/-!
# Cubic exclusion from a marked full-normalizer bound

A faithful representation containing a normal marked model embeds, after
conjugating through the marked linear equivalence, into that model's full
linear normalizer. The same elementary subgroup then retains both its rank
and fixed codimension. Strict normalizer bounds therefore contradict a cubic
ratio at most two for the original actor.

This is the actor-preserving transport needed by the moved-pair argument in
Aschbacher–Smith D.3.5, printed pp.195–196.
-/

@[expose] public noncomputable section
namespace Representation.BinaryOffender
open Subgroup
variable {K H V W : Type*} [Group K] [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- Strict bounds for the entire model normalizer exclude the same cubic bound
for a faithful actor containing the marked model as a normal action. -/
theorem not_cubicRatio_le_two_of_normal_model
    (τ : Representation (ZMod 2) H V) (σ : Representation (ZMod 2) K W)
    (hτ : Function.Injective τ) (i : K →* H) [i.range.Normal]
    (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (τ (i g) v) = σ g (E v))
    (hstrict : ∀ B : Subgroup (linearNormalizer σ), IsElementaryTwo B →
      2 * rank B < fixedCodim (normalizerRepresentation σ) B) :
    ¬ cubicRatio τ ≤ 2 := by
  have he : actionImage (τ.comp i) = actionImage (τ.comp i.range.subtype) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨⟨i g, ⟨g, rfl⟩⟩, Units.ext rfl⟩
    · rintro ⟨⟨_, g, rfl⟩, rfl⟩
      exact ⟨g, Units.ext rfl⟩
  have hown : actionImage τ ≤ linearNormalizer (τ.comp i) := by
    have hh := actionImage_le_linearNormalizer τ i.range
    unfold linearNormalizer at hh ⊢
    rwa [← he] at hh
  let c := BinaryNormalizerResidual.unitConj E
  let fUnit : H →* (Module.End (ZMod 2) W)ˣ := c.toMonoidHom.comp τ.asGroupHom
  have hfmem (h : H) : fUnit h ∈ linearNormalizer σ := by
    rw [← BinaryNormalizerResidual.normalizer_map (τ.comp i) σ
      (MulEquiv.refl K) E hE]
    exact Subgroup.mem_map_of_mem c.toMonoidHom (hown ⟨h, rfl⟩)
  let f : H →* linearNormalizer σ := fUnit.codRestrict _ hfmem
  have hf : Function.Injective f := by
    intro x y h
    apply hτ
    exact congrArg Units.val (c.injective (congrArg Subtype.val h))
  have hfv (g : H) (v : V) :
      E (τ g v) = normalizerRepresentation σ (f g) (E v) := by
    change E (τ g v) = E (τ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  intro hcubic
  obtain ⟨A, hA, _, hnum⟩ := (cubicRatio_le_nat_iff τ 2).mp hcubic
  let := hA.2
  have hB : IsElementaryTwo (A.map f) := by
    refine ⟨?_, IsElementaryAbelian.map f⟩
    intro hb
    apply hA.1
    apply Subgroup.map_injective hf
    simpa only [Subgroup.map_bot] using hb
  have hh := hstrict (A.map f) hB
  rw [rank_map_injective f hf,
    ← fixedCodim_map_equivariant τ (normalizerRepresentation σ) f E hfv] at hh
  omega
end Representation.BinaryOffender
