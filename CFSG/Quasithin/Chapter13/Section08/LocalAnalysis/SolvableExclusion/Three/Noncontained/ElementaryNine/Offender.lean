module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.ElementaryNine.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.ElementaryNine.Support
public import Theory.Representation.AffineNine.CubicBound
public import Theory.SpecificGroups.GL2.ThreeResidualImages.Basic

/-!
# A direct offender obstruction for the marked nine-group action

Suppose conjugation on an actual normal nine-group contains SL₂(3). Its
binary character spaces have eight equal positive nontrivial dimensions.
To obtain this fact without assuming that the ambient group splits, use the
semidirect-product cover formed from the marked conjugation action. Only
its translation restriction needs to be faithful; its full action may have
kernel. Restriction of these same weights to a faithfully acting elementary
two-subgroup allows the proved affine-nine dual-orbit estimate to apply.

The resulting strict fixed-codimension inequality rules out every ratio-two
actor which acts faithfully on the original nine-group. Duality also proves
the eight-dimensional lower bound on the actual commutator support. The
source applications in the parent module supply the selected actor's
faithfulness and quadratic ratio; local SL₂(3) image recognition remains
separate. No D.2.17 generation, Fitting or indecomposability conclusion is
assumed, and no isomorphism of the whole ambient group to a split affine
model is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.13, printed p.951 (PDF p.968). The character and orbit estimates are
the proved affine-nine mathematics also used for 15.4.10, printed p.1159.
-/

public section
open Subgroup Representation Representation.BinaryOffender Representation.AffineNine
open scoped IsMulCommutative MatrixGroups TensorProduct
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Noncontained.ElementaryNine

variable {K : Type*} [Group K] {P : Subgroup K}

private def affineLift (a : ConjugationCoordinates P) {D : Type*} [Group D]
    (f : D →* K) : Affine (a.action.comp f) →* K :=
  SemidirectProduct.lift (P.subtype.comp a.coordinate.symm.toMonoidHom) f (by
    intro d
    apply MonoidHom.ext
    intro x
    change (a.coordinate.symm (naturalAction (a.action (f d)) x) : K) =
      f d * (a.coordinate.symm x : K) * (f d)⁻¹
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype, MulAut.conj_apply, MulEquiv.apply_symm_apply] using
      (a.conjugates (f d) (a.coordinate.symm x)).symm)

private theorem translation_lift {E V D : Type*} [Field E] [AddCommGroup V]
    [Module E V] [Group D] (a : ConjugationCoordinates P)
    (ρ : Representation E K V) (f : D →* K) :
    translationRepresentation (a.action.comp f) (ρ.comp (affineLift a f)) =
      ρ.comp (P.subtype.comp a.coordinate.symm.toMonoidHom) := by
  apply MonoidHom.ext
  intro t
  apply LinearMap.ext
  intro v
  change ρ (affineLift a f (SemidirectProduct.inl t)) v = ρ (a.coordinate.symm t) v
  rw [affineLift, SemidirectProduct.lift_inl]
  rfl

private theorem translation_nonzero_weight {E V D : Type*} [Field E] [IsAlgClosed E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V] [Group D]
    (j : D →* LinearGroup) (ρ : Representation E (Affine j) V)
    (hf : Function.Injective (translationRepresentation j ρ))
    (ho : (Nat.card Translation : E) ≠ 0) :
    ∃ χ : Translation →* Eˣ, χ ≠ 1 ∧
      (translationRepresentation j ρ).characterWeightSpace χ ≠ ⊥ := by
  let σ := translationRepresentation j ρ
  by_contra h
  push Not at h
  have hle : (⨆ χ : σ.CharacterWeight, σ.characterWeightSpace χ.val) ≤
      σ.characterWeightSpace 1 := by
    refine iSup_le fun χ => ?_
    by_cases hχ : χ.val = 1
    · rw [hχ]
    · rw [h χ.val hχ]
      exact bot_le
  have htop : σ.characterWeightSpace 1 = ⊤ := by
    apply top_unique
    rw [← σ.iSup_characterWeightSpace_eq_top ho]
    exact hle
  let t : Translation := Multiplicative.ofAdd (fun _ : Fin 2 => (1 : ZMod 3))
  have ht : t ≠ 1 := by decide
  apply ht
  apply hf
  ext v
  have hv : v ∈ σ.characterWeightSpace 1 := htop ▸ Submodule.mem_top
  have he : σ t v = v := by
    simpa only [characterWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff,
      MonoidHom.one_apply, Units.val_one, one_smul] using (show ∀ k,
      v ∈ Module.End.eigenspace (σ k) ((1 : Translation →* Eˣ) k : E) from
      by simpa only [characterWeightSpace, Submodule.mem_iInf] using hv) t
  simpa only [map_one, Module.End.one_apply] using he

private theorem special_character_transitive (a : ConjugationCoordinates P)
    (hSL : Matrix.GeneralLinearGroup.threeSpecialLinear ≤ a.action.range) :
    ∀ χ ψ : Translation →* algebraicClosureE9ˣ, χ ≠ 1 → ψ ≠ 1 →
      ∃ k : K, conjugateCharacter (a.action.comp (MonoidHom.id K)) k χ = ψ := by
  apply characterTransitive_of_coordinates _
    { equiv := algebraicClosureTranslationCharacterEquiv
      equivariant := fun k w => algebraicClosureTranslationCharacterEquiv_equivariant (a.action k) w }
  intro w z hw hz
  obtain ⟨g, hg⟩ := dualPerm_special_transitive w z hw hz
  obtain ⟨k, hk⟩ := hSL (Matrix.SpecialLinearGroup.coeToGL_det g)
  exact ⟨k, by simpa only [MonoidHom.comp_apply, MonoidHom.id_apply, hk] using hg⟩

private noncomputable def ambient_uniform {V : Type*} [AddCommGroup V]
    [Module algebraicClosureE9 V] [FiniteDimensional algebraicClosureE9 V]
    (a : ConjugationCoordinates P) (ρ : Representation algebraicClosureE9 K V)
    (hf : Function.Injective ρ)
    (hSL : Matrix.GeneralLinearGroup.threeSpecialLinear ≤ a.action.range) :
    UniformWeights (a.action.comp (MonoidHom.id K))
      (ρ.comp (affineLift a (MonoidHom.id K))) := by
  let j := a.action.comp (MonoidHom.id K)
  let σ := ρ.comp (affineLift a (MonoidHom.id K))
  have hi : Function.Injective (translationRepresentation j σ) := by
    rw [translation_lift]
    exact hf.comp (P.subtype_injective.comp a.coordinate.symm.injective)
  let hex := translation_nonzero_weight j σ hi algebraicClosure_translation_card_ne_zero
  let χ₀ := Classical.choose hex
  have hχ₀ := (Classical.choose_spec hex).1
  have hn := (Classical.choose_spec hex).2
  refine ⟨Module.finrank algebraicClosureE9 ((translationRepresentation j σ).characterWeightSpace χ₀),
    ?_, ?_⟩
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hv⟩, by simpa using hv0⟩
  · intro χ hχ
    obtain ⟨k, hk⟩ := special_character_transitive a hSL χ₀ χ hχ₀ hχ
    rw [← hk]
    exact (finrank_characterWeightSpace_conjugate j σ k χ₀).symm

private noncomputable def restricted_uniform {V D : Type*} [AddCommGroup V]
    [Module algebraicClosureE9 V] [FiniteDimensional algebraicClosureE9 V] [Group D]
    (a : ConjugationCoordinates P) (ρ : Representation algebraicClosureE9 K V)
    (hf : Function.Injective ρ)
    (hSL : Matrix.GeneralLinearGroup.threeSpecialLinear ≤ a.action.range) (f : D →* K) :
    UniformWeights (a.action.comp f) (ρ.comp (affineLift a f)) := by
  let u := ambient_uniform a ρ hf hSL
  refine ⟨u.nontrivialDim, u.positive, ?_⟩
  intro χ hχ
  have hu := u.nontrivial_finrank χ hχ
  rw [translation_lift] at hu ⊢
  exact hu

private theorem eight_fixedCodim_of_special_image [Finite K]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (a : ConjugationCoordinates P) (ρ : Representation (ZMod 2) K V)
    (hf : Function.Injective ρ)
    (hSL : Matrix.GeneralLinearGroup.threeSpecialLinear ≤ a.action.range) :
    8 ≤ fixedCodim ρ P := by
  classical
  let j := a.action.comp (MonoidHom.id K)
  let σ : Representation (ZMod 2) (Affine j) V := ρ.comp (affineLift a (MonoidHom.id K))
  let τ := σ.extendScalars algebraicClosureE9
  have hτ : τ = (ρ.extendScalars algebraicClosureE9).comp (affineLift a (MonoidHom.id K)) := rfl
  let u : UniformWeights j τ := hτ ▸ restricted_uniform a (ρ.extendScalars algebraicClosureE9)
    ((extendScalars_faithful_iff algebraicClosureE9 ρ).mp hf) hSL (MonoidHom.id K)
  let U := planeWeightSpace j τ
  let d := fun w => Module.finrank algebraicClosureE9 (U w)
  have hd : ∀ w, w ≠ 0 → d w = u.nontrivialDim := planeWeightSpace_finrank_nonzero j τ u
  have hs : ∑ w ∈ (Finset.univ : Finset Plane).erase 0, d w = 8 * u.nontrivialDim := by
    calc
      _ = ∑ _w ∈ (Finset.univ : Finset Plane).erase 0, u.nontrivialDim :=
        Finset.sum_congr rfl (fun w hw => hd w (Finset.mem_erase.mp hw).1)
      _ = _ := by simp
  have he := Finset.sum_erase_add (Finset.univ : Finset Plane) d (Finset.mem_univ 0)
  rw [hs] at he
  have ht := finrank_eq_sum U (planeWeightSpace_independent j τ) (iSup_planeWeightSpace_eq_top j τ)
  have hdim : Module.finrank (ZMod 2) V = d 0 + 8 * u.nontrivialDim := by
    have hb : Module.finrank algebraicClosureE9 (algebraicClosureE9 ⊗[ZMod 2] V) =
        Module.finrank (ZMod 2) V := Module.finrank_baseChange
    rw [hb] at ht
    exact ht.trans (he.symm.trans (Nat.add_comm _ _))
  have hfix : (translationRepresentation j σ).invariants = fixedSpace ρ P := by
    rw [translation_lift]
    ext v
    change (∀ t : Translation, ρ (a.coordinate.symm t) v = v) ↔
      (∀ p : P, ρ p v = v)
    constructor
    · intro h p
      simpa only [MulEquiv.symm_apply_apply] using h (a.coordinate p)
    · intro h t
      exact h (a.coordinate.symm t)
  have hz : d 0 = Module.finrank (ZMod 2) (fixedSpace ρ P) := by
    change Module.finrank algebraicClosureE9 (planeWeightSpace j (σ.extendScalars algebraicClosureE9) 0) = _
    rw [finrank_planeWeightSpace_zero_extendScalars, hfix]
  have hc := fixedCodim_add_finrank ρ P
  have hp := u.positive
  omega

/-- Recognition of the actual special-linear image forces eight dimensions
in the actual P-moved subspace, without any hyperplane-orbit premise. -/
theorem support_finrank_ge_eight_of_special_image [Finite K]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (a : ConjugationCoordinates P) (ρ : Representation (ZMod 2) K V)
    (hf : Function.Injective ρ)
    (hSL : Matrix.GeneralLinearGroup.threeSpecialLinear ≤ a.action.range) :
    8 ≤ Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ P) := by
  have h := eight_fixedCodim_of_special_image a ρ.dual (dual_injective ρ hf) hSL
  have he : fixedCodim ρ.dual P = Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ P) := by
    rw [← coinvariants_eq_support ρ P]
    exact finrank_quotient_dual_invariants_eq_commutator (ρ.comp P.subtype)
  rwa [he] at h

/-- The original representation has no ratio-two elementary actor faithful
on the marked nine-group when its conjugation image contains SL₂(3). -/
theorem strict_fixedCodim_of_special_image [Finite K]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (a : ConjugationCoordinates P) (ρ : Representation (ZMod 2) K V)
    (hf : Function.Injective ρ)
    (hSL : Matrix.GeneralLinearGroup.threeSpecialLinear ≤ a.action.range)
    (A : Subgroup K) (hA : IsElementaryTwo A)
    (hcent : A ⊓ centralizer (P : Set K) = ⊥) :
    2 * rank A < fixedCodim ρ A := by
  let j := a.action.comp A.subtype
  let σ : Representation (ZMod 2) (Affine (a.action.comp A.subtype)) V :=
    ρ.comp (affineLift a A.subtype)
  let f : A →* Affine j := SemidirectProduct.inr
  let B := (⊤ : Subgroup A).map f
  let : IsElementaryAbelian 2 A := hA.2
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA.1
  let : IsElementaryAbelian 2 (⊤ : Subgroup A) :=
    { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
        Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 A) x.val) }
  have hB : IsElementaryTwo B := by
    refine ⟨?_, IsElementaryAbelian.map f⟩
    intro hb
    have hb' : (⊤ : Subgroup A) = ⊥ := (Subgroup.map_injective SemidirectProduct.inr_injective)
      (hb.trans (Subgroup.map_bot f).symm)
    exact top_ne_bot hb'
  have hσ : σ.extendScalars algebraicClosureE9 =
      (ρ.extendScalars algebraicClosureE9).comp (affineLift a A.subtype) := rfl
  have u : UniformWeights j (σ.extendScalars algebraicClosureE9) := by
    rw [hσ]
    exact restricted_uniform a (ρ.extendScalars algebraicClosureE9)
      ((extendScalars_faithful_iff algebraicClosureE9 ρ).mp hf) hSL A.subtype
  have hbound := strict_fixedCodim_of_geometry j (a.injective_on A hcent) σ u B hB
  have hr : rank B = rank A := by
    rw [rank_map_injective f SemidirectProduct.inr_injective]
    unfold rank
    rw [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toEquiv]
  have hc : fixedSpace σ B = fixedSpace ρ A := by
    rw [← fixedSpace_comp_map σ f]
    have he : σ.comp f = ρ.comp A.subtype := by
      ext x v
      simp only [σ, f, MonoidHom.comp_apply, affineLift, SemidirectProduct.lift_inr]
    rw [he, fixedSpace_comp_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcodim : fixedCodim σ B = fixedCodim ρ A := by
    unfold fixedCodim
    rw [hc]
  rwa [hr, hcodim] at hbound

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Noncontained.ElementaryNine
end
