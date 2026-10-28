module

public import Theory.Representation.HermitianTensorThree.ImageOuter.OuterRank.Intrinsic

/-!
# Normalizer conjugation of the source overgroup

Conjugating by the full binary normalizer transports M, its residual image,
and its faithful action together. The conjugating element need not belong
to M or to the image. Element centralizers inside the image are transported
by the same conjugation, ready for the marked field-swap calculation.

Source: Aschbacher–Smith, H.4.4(6), printed p.381; the standing equation
L = M∞ is on printed p.377.
-/

@[expose] public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter.OuterRank
open Subgroup
variable (n : ℕ) [NeZero n]

/-- Normalizer conjugation preserves the actual equation L = M∞. -/
theorem sourceOvergroup_map_conj
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)
    (c : Space n ≃ₗ[ZMod 2] Space n) (hc : c ∈ binaryNormalizer n) :
    SourceOvergroup n (M.map (MulAut.conj c).toMonoidHom) := by
  let f := (MulAut.conj c).toMonoidHom
  let e := M.equivMapOfInjective f (MulAut.conj c).injective
  have hres := map_solvableResidual_eq e.toMonoidHom e.surjective
  change (solvableResidual (M.map f)).map (M.map f).subtype = binaryImage n
  calc
    (solvableResidual (M.map f)).map (M.map f).subtype =
        ((solvableResidual M).map e.toMonoidHom).map (M.map f).subtype := by rw [hres]
    _ = ((solvableResidual M).map M.subtype).map f := by
      rw [map_map, map_map]
      rfl
    _ = (binaryImage n).map f := by rw [hM]
    _ = binaryImage n := mem_normalizer_iff_map_conj_eq.mp hc

/-- The subgroup equivalence intertwines the original faithful binary actions. -/
theorem overgroupAction_conj
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    (c : Space n ≃ₗ[ZMod 2] Space n) (g : M) (X : Space n) :
    overgroupAction n (M.map (MulAut.conj c).toMonoidHom)
      (M.equivMapOfInjective _ (MulAut.conj c).injective g) (c X) =
        c (overgroupAction n M g X) := by
  change (c * g.val * c⁻¹) (c X) = c (g.val X)
  simp

private theorem map_centralizer_singleton {G : Type*} [Group G] (e : G ≃* G) (i : G) :
    (centralizer ({i} : Set G)).map e.toMonoidHom = centralizer ({e i} : Set G) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e x * e i = e i * e x
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hx)
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx

/-- The literal image centralizer is carried to the literal marked centralizer. -/
theorem imageCentralizer_map_conj
    (i c : Space n ≃ₗ[ZMod 2] Space n) (hc : c ∈ binaryNormalizer n)
    (hi : MulAut.conj c i = fieldSwapBinary n) :
    (binaryImage n ⊓ centralizer ({i} : Set (Space n ≃ₗ[ZMod 2] Space n))).map
      (MulAut.conj c).toMonoidHom =
        binaryImage n ⊓ centralizer ({fieldSwapBinary n} : Set _) := by
  have hc' : (binaryImage n).map (MulAut.conj c).toMonoidHom = binaryImage n :=
    mem_normalizer_iff_map_conj_eq.mp hc
  rw [map_inf _ _ _ (MulAut.conj c).injective, hc', map_centralizer_singleton, hi]

/-- The centralizer comparison retains the actual conjugating map. -/
def imageCentralizerEquivOfConj
    (i c : Space n ≃ₗ[ZMod 2] Space n) (hc : c ∈ binaryNormalizer n)
    (hi : MulAut.conj c i = fieldSwapBinary n) :
    ↥(binaryImage n ⊓ centralizer ({i} : Set (Space n ≃ₗ[ZMod 2] Space n))) ≃*
      ↥(binaryImage n ⊓ centralizer ({fieldSwapBinary n} : Set _)) :=
  ((binaryImage n ⊓ centralizer ({i} : Set (Space n ≃ₗ[ZMod 2] Space n))).equivMapOfInjective
    (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans
      (MulEquiv.subgroupCongr (imageCentralizer_map_conj n i c hc hi))

theorem imageCentralizerEquivOfConj_apply
    (i c : Space n ≃ₗ[ZMod 2] Space n) (hc : c ∈ binaryNormalizer n)
    (hi : MulAut.conj c i = fieldSwapBinary n)
    (g : ↥(binaryImage n ⊓ centralizer ({i} : Set (Space n ≃ₗ[ZMod 2] Space n)))) :
    (imageCentralizerEquivOfConj n i c hc hi g).val = c * g.val * c⁻¹ := rfl

/-- An outer involution is reduced to the marked swap in the transported source
  overgroup, with the residual equation preserved. Fusion remains explicit. -/
theorem source_outer_involution_transport
    (hFusion : ∀ i ∈ binaryNormalizer n, orderOf i = 2 → i ∉ binaryImage n →
      ∃ c ∈ binaryNormalizer n, MulAut.conj c i = fieldSwapBinary n)
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)
    (i : M) (hi : orderOf i = 2) (hiL : i.val ∉ binaryImage n) :
    ∃ c ∈ binaryNormalizer n,
      MulAut.conj c i.val = fieldSwapBinary n ∧
      SourceOvergroup n (M.map (MulAut.conj c).toMonoidHom) ∧
      fieldSwapBinary n ∈ M.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨c, hc, hci⟩ := hFusion i.val
    (sourceOvergroup_le_normalizer n M hM i.property) ((orderOf_coe i).trans hi) hiL
  exact ⟨c, hc, hci, sourceOvergroup_map_conj n M hM c hc, i.val, i.property, hci⟩

end Representation.HermitianTensorThree.ImageOuter.OuterRank
