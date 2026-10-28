module
public import Theory.Representation.AffineNine.CubicBound
public import Theory.Representation.AbelianWeightAutomizer
public import Theory.SpecificGroups.GL2.ThreeResidualImages.Basic

/-!
# Four moved dimensions from the eight nonzero ternary weights

Only the restriction to the translation group is required to be faithful.
Thus this result applies to the pullback of a representation along
P ⋊ X → X, without assuming that P has a complement in X. The SL₂(3)
image makes the eight nonzero character spaces have equal positive
size. Inversion pairs them, and projection to five orbit representatives
bounds the fixed space by the zero weight plus four nonzero weights.
Scalar extension preserves fixed dimensions, giving the binary bound.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.5.20, printed p.923 (PDF p.940).
-/

public section
open scoped BigOperators TensorProduct
open Subgroup Matrix
open Matrix.GeneralLinearGroup
namespace Representation.NormalNineCentralInvolution
open AffineNine BinaryOffender
noncomputable section

private def inversionRepresentatives : Finset Plane :=
  {0, ![1, 0], ![0, 1], ![1, 1], ![1, 2]}

private theorem inversion_cover (w : Plane) :
    ∃ r ∈ inversionRepresentatives, r = w ∨ -r = w := by
  decide +revert

private theorem inversion_card : inversionRepresentatives.card = 5 := by decide

private theorem dual_central (w : Plane) : dualPerm threeCentral w = -w := by
  have hinv : threeCentral⁻¹ = threeCentral := inv_eq_of_mul_eq_one_left (by
    apply Units.ext
    decide)
  have he : (threeCentral⁻¹).val.transpose = -(1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
    rw [hinv]
    decide
  rw [dualPerm_apply, he, Matrix.neg_mulVec, Matrix.one_mulVec]

private theorem uniform_of_translation_faithful
    {L V : Type*} [Group L] [AddCommGroup V]
    [Module algebraicClosureE9 V] [FiniteDimensional algebraicClosureE9 V]
    (j : L →* LinearGroup) (ρ : Representation algebraicClosureE9 (Affine j) V)
    (hf : Function.Injective (translationRepresentation j ρ))
    (hSL : threeSpecialLinear ≤ j.range) : Nonempty (UniformWeights j ρ) := by
  let σ := translationRepresentation j ρ
  have hex : ∃ χ : σ.CharacterWeight, χ.val ≠ 1 := by
    by_contra! hn
    have ht : (Multiplicative.ofAdd (![1, 0] : Plane) : Translation) = 1 := by
      apply eq_of_characterWeight_values σ hf algebraicClosure_translation_card_ne_zero
      intro χ
      simp [hn χ]
    exact (by decide : (Multiplicative.ofAdd (![1, 0] : Plane) : Translation) ≠ 1) ht
  obtain ⟨χ, hχ⟩ := hex
  refine ⟨⟨Module.finrank algebraicClosureE9 (σ.characterWeightSpace χ.val),
    lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.mpr χ.property), ?_⟩⟩
  intro ψ hψ
  have htrans : ∀ χ ψ : Translation →* algebraicClosureE9ˣ, χ ≠ 1 → ψ ≠ 1 →
      ∃ l : L, conjugateCharacter j l χ = ψ := by
    apply characterTransitive_of_coordinates j
      { equiv := algebraicClosureTranslationCharacterEquiv
        equivariant := fun l w => algebraicClosureTranslationCharacterEquiv_equivariant (j l) w }
    intro w z hw hz
    obtain ⟨s, hs⟩ := dualPerm_special_transitive w z hw hz
    obtain ⟨l, hl⟩ := hSL (show SpecialLinearGroup.toGL s ∈ threeSpecialLinear from
      SpecialLinearGroup.coeToGL_det s)
    exact ⟨l, by rw [hl]; exact hs⟩
  obtain ⟨l, hl⟩ := htrans χ.val ψ hχ hψ
  rw [← hl]
  exact (finrank_characterWeightSpace_conjugate j ρ l χ.val).symm

private theorem sum_uniform (d : Plane → ℕ) (m : ℕ)
    (hd : ∀ w, w ≠ 0 → d w = m) (S : Finset Plane) (h0 : 0 ∈ S) :
    ∑ w ∈ S, d w = d 0 + (S.card - 1) * m := by
  classical
  have hs : ∑ w ∈ S.erase 0, d w = (S.erase 0).card * m := by
    calc
      _ = ∑ _w ∈ S.erase 0, m := Finset.sum_congr rfl (fun w hw => hd w (Finset.mem_erase.mp hw).1)
      _ = _ := by simp
  have he := Finset.sum_erase_add S d h0
  rw [hs, Finset.card_erase_of_mem h0] at he
  omega

/-- The bound only requires faithfulness on translations, even if the
external semidirect product has a kernel on the whole representation. -/
theorem affine_pullback_bound
    {L V : Type*} [Group L] [Finite L] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (j : L →* LinearGroup) (ρ : Representation (ZMod 2) (Affine j) V)
    (hf : Function.Injective (translationRepresentation j ρ))
    (hSL : threeSpecialLinear ≤ j.range) (a : L) (ha : j a = threeCentral) :
    4 ≤ fixedCodim ρ (zpowers (SemidirectProduct.inr a)) := by
  classical
  let σ := ρ.extendScalars algebraicClosureE9
  obtain ⟨u⟩ := uniform_of_translation_faithful j σ
    ((extendScalars_faithful_iff algebraicClosureE9 (translationRepresentation j ρ)).mp hf) hSL
  let U := planeWeightSpace j σ
  let d := fun w => Module.finrank algebraicClosureE9 (U w)
  let m := u.nontrivialDim
  have hm : 0 < m := u.positive
  have hd : ∀ w, w ≠ 0 → d w = m := planeWeightSpace_finrank_nonzero j σ u
  let A := zpowers (SemidirectProduct.inr a : Affine j)
  let p : A → Equiv.Perm Plane := fun b => dualPerm (linearPart j b)
  have hS : ∀ w, ∃ r ∈ inversionRepresentatives, ∃ b : A, p b r = w := by
    intro w
    obtain ⟨r, hr, he | he⟩ := inversion_cover w
    · refine ⟨r, hr, 1, ?_⟩
      simpa [p, linearPart, dualPerm] using he
    · refine ⟨r, hr, ⟨SemidirectProduct.inr a, mem_zpowers _⟩, ?_⟩
      change dualPerm (j a) r = w
      rw [ha, dual_central, he]
  have hi := planeWeightSpace_independent j σ
  have ht := iSup_planeWeightSpace_eq_top j σ
  have hfixed := finrank_invariants_le_representatives (σ.comp A.subtype) U hi ht p
    (fun b w v hv => mem_planeWeightSpace_apply j σ b w v hv) inversionRepresentatives hS
  have hfixed' : Module.finrank algebraicClosureE9 (Representation.invariants (σ.comp A.subtype)) ≤
      d 0 + 4 * m := by
    calc
      _ ≤ ∑ r : inversionRepresentatives, d r := hfixed
      _ = ∑ r ∈ inversionRepresentatives, d r := Finset.sum_coe_sort _ _
      _ = _ := by rw [sum_uniform d m hd _ (by decide), inversion_card]
  have htotal : Module.finrank algebraicClosureE9 (algebraicClosureE9 ⊗[ZMod 2] V) =
      d 0 + 8 * m := by
    have hh := finrank_eq_sum U hi ht
    rw [sum_uniform d m hd Finset.univ (Finset.mem_univ _)] at hh
    simpa only [Finset.card_univ, card_plane] using hh
  have hbase : Module.finrank algebraicClosureE9 (Representation.invariants (σ.comp A.subtype)) =
      Module.finrank (ZMod 2) (fixedSpace ρ A) :=
    finrank_invariants_extendScalars_eq_of_finite (ρ.comp A.subtype)
  rw [hbase] at hfixed'
  rw [Module.finrank_baseChange] at htotal
  have hc := fixedCodim_add_finrank ρ A
  change 4 ≤ fixedCodim ρ A
  omega

end
end Representation.NormalNineCentralInvolution
