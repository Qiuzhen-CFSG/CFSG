module
public import Theory.LinearAlgebra.BinaryFourAlternatingEight
public import Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryPermutation.ThreeTensor
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic

/-!
# Natural automorphisms from one or two natural A₆ constituents

The binary four-space comparison GL₄(2) ≃ A₈ bounds the normalizer of
A₆ by 720; the natural S₆ supplies equality. A twisted intertwiner therefore
induces an automorphism in the natural S₆. For two copies, a nonzero matrix
block is an isomorphism of simple constituents, reducing to the same result.
Normality of S₆ in Aut(A₆) removes dependence on the chosen A₆ marking.

The tensor restriction below uses the actual natural two-space on three
letters, whose alternating subgroup is Z₃. It handles the component action
in G.11.2(10), while one copy handles G.11.2(2). Recognition of a source
module as these modules is deliberately separate.

Source: Aschbacher--Smith G.11.2(2),(10), pp.364--367, and K.1.1, p.452.
The normalizer argument is the lower-layer version of ChapterK's
RecognitionInputs.Six.normalizer. The imported GL₄(2) ≃ A₈ comparison retains
its ATLAS attribution and license in Theory.LinearAlgebra.BinaryFourAlternatingEight.
-/

public noncomputable section
open Subgroup Representation
namespace Representation.BinaryAlternatingSixNaturalNormalizer
open AlternatingSix.ShadowLocal

abbrev Vector := BinaryPermutation.natural (Fin 6)
abbrev action := BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6)

@[expose] def naturalLinearAction : Equiv.Perm (Fin 6) →* (Vector ≃ₗ[ZMod 2] Vector) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Vector).toMonoidHom.comp
    (BinaryPermutation.naturalRepresentation (Fin 6)).asGroupHom

@[expose] def alternatingLinearImage :=
  (naturalLinearAction.comp (alternatingGroup (Fin 6)).subtype).range

private theorem naturalLinearAction_injective : Function.Injective naturalLinearAction := by
  intro g h he
  apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
  apply LinearMap.ext
  intro v
  exact LinearEquiv.congr_fun he v

private theorem natural_alternating_action_injective :
    Function.Injective (naturalLinearAction.comp (alternatingGroup (Fin 6)).subtype) :=
  naturalLinearAction_injective.comp Subtype.val_injective

private theorem natural_range_le_normalizer :
    naturalLinearAction.range ≤ Subgroup.normalizer (alternatingLinearImage : Set _) := by
  change naturalLinearAction.range ≤ Subgroup.normalizer
    ((naturalLinearAction.comp (alternatingGroup (Fin 6)).subtype).range : Set _)
  rw [MonoidHom.range_comp, range_subtype]
  have h := Subgroup.le_normalizer_map (H := alternatingGroup (Fin 6)) naturalLinearAction
  simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map] using h

/-- The full linear normalizer of the natural A₆ is the natural S₆. -/
theorem normalizer :
    Subgroup.normalizer (alternatingLinearImage : Set _) = naturalLinearAction.range := by
  have hd : Module.finrank (ZMod 2) Vector = 4 := by
    rw [BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    rfl
  let e := BinaryFourAlternatingEight.linearEquivAlternatingEight hd
  let : Finite (Vector ≃ₗ[ZMod 2] Vector) := Finite.of_injective e e.injective
  let f := e.toMonoidHom.comp
    (naturalLinearAction.comp (alternatingGroup (Fin 6)).subtype)
  have hf : Function.Injective f := e.injective.comp natural_alternating_action_injective
  have hr : f.range = alternatingLinearImage.map e.toMonoidHom := MonoidHom.range_comp _ _
  have hn := Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.normalizer_card_le f hf
  rw [hr, ← Subgroup.map_equiv_normalizer_eq, Subgroup.card_map_of_injective e.injective] at hn
  have hs : Nat.card naturalLinearAction.range = 720 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective naturalLinearAction_injective).toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  exact (Subgroup.eq_of_le_of_card_ge natural_range_le_normalizer (by omega)).symm

theorem natural_of_intertwiner (α : MulAut A6) (u : Vector ≃ₗ[ZMod 2] Vector)
    (hu : ∀ a v, u (action a v) = action (α a) (u v)) : α ∈ natural := by
  let a := naturalLinearAction.comp (alternatingGroup (Fin 6)).subtype
  have he : (MulAut.conj u).toMonoidHom.comp a = a.comp α.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply LinearEquiv.ext
    intro v
    change u (action x (u.symm v)) = action (α x) v
    rw [hu, u.apply_symm_apply]
  have hn : u ∈ Subgroup.normalizer (alternatingLinearImage : Set _) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change a.range.map (MulAut.conj u).toMonoidHom = a.range
    rw [← MonoidHom.range_comp, he, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr α.surjective,
      ← MonoidHom.range_eq_map]
  rw [Representation.BinaryAlternatingSixNaturalNormalizer.normalizer] at hn
  obtain ⟨s, hs⟩ := hn
  refine ⟨s, ?_⟩
  apply MulEquiv.ext
  intro x
  apply natural_alternating_action_injective
  have hx := DFunLike.congr_fun he x
  change u * a x * u⁻¹ = a (α x) at hx
  rw [← hs] at hx
  change naturalLinearAction ((permutationAction s x : A6) : Equiv.Perm (Fin 6)) = _
  change naturalLinearAction (s * (x : Equiv.Perm (Fin 6)) * s⁻¹) = _
  simpa only [a, MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_inv] using hx

theorem natural_conjugation_iff (β α : MulAut A6) :
    β * α * β⁻¹ ∈ natural ↔ α ∈ natural := by
  let : natural.Normal := Subgroup.normal_of_index_eq_two
    GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index
  constructor
  · intro h
    have hh := Subgroup.Normal.conj_mem (inferInstance : natural.Normal) _ h β⁻¹
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_inv,
      inv_mul_cancel, mul_one] using hh
  · intro h
    exact Subgroup.Normal.conj_mem inferInstance _ h β

/-- A nonzero block of a twisted intertwiner on two copies gives an
intertwiner on the simple constituent. -/
private theorem intertwiner_of_pair {k D E : Type*} [Field k] [Group D]
    [AddCommGroup E] [Module k E]
    (σ : Representation k D E) [IsIrreducible σ]
    (α : MulAut D) (u : (E × E) ≃ₗ[k] (E × E))
    (hu : ∀ a v, u ((σ.prod σ) a v) = (σ.prod σ) (α a) (u v)) :
    ∃ f : E ≃ₗ[k] E, ∀ a v, f (σ a v) = σ (α a) (f v) := by
  let τ := σ.comp α.toMonoidHom
  let : IsIrreducible τ :=
    (irreducible_comp_surjective_iff α.toMonoidHom α.surjective σ).mpr inferInstance
  let f : IntertwiningMap σ τ := {
    toLinearMap := (LinearMap.fst k E E).comp
      (u.toLinearMap.comp (LinearMap.inl k E E))
    isIntertwining' a := by
      ext v
      simpa [Representation.prod, τ] using congrArg Prod.fst (hu a (v, 0)) }
  let g : IntertwiningMap σ τ := {
    toLinearMap := (LinearMap.snd k E E).comp
      (u.toLinearMap.comp (LinearMap.inl k E E))
    isIntertwining' a := by
      ext v
      simpa [Representation.prod, τ] using congrArg Prod.snd (hu a (v, 0)) }
  have hne : f ≠ 0 ∨ g ≠ 0 := by
    by_contra! hz
    let : Nontrivial E := Subrepresentation.irreducible_module_nontrivial σ
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    apply hv
    have hzero : u (v, 0) = 0 := by
      apply Prod.ext
      · exact congrArg (fun h : IntertwiningMap σ τ => h v) hz.1
      · exact congrArg (fun h : IntertwiningMap σ τ => h v) hz.2
    exact congrArg Prod.fst (u.injective (hzero.trans u.map_zero.symm))
  rcases hne with hf | hg
  · let e := f.ofBijective ((IsIrreducible.bijective_or_eq_zero f).resolve_right hf)
    exact ⟨e.toLinearEquiv, fun a v => LinearMap.congr_fun (e.isIntertwining' a) v⟩
  · let e := g.ofBijective ((IsIrreducible.bijective_or_eq_zero g).resolve_right hg)
    exact ⟨e.toLinearEquiv, fun a v => LinearMap.congr_fun (e.isIntertwining' a) v⟩

theorem natural_of_pair_intertwiner (α : MulAut A6)
    (u : (Vector × Vector) ≃ₗ[ZMod 2] (Vector × Vector))
    (hu : ∀ a v, u ((action.prod action) a v) =
      (action.prod action) (α a) (u v)) : α ∈ natural := by
  let : IsIrreducible action := BinaryPermutation.alternatingNatural_isIrreducible (by decide)
  obtain ⟨f,hf⟩ := intertwiner_of_pair action α u hu
  exact natural_of_intertwiner α f hf

/-- Actual coordinates for one or two copies of the binary natural A₆-module.
The group marking may differ from a caller's independently chosen marking. -/
@[expose] def HasNaturalCoordinates {D E : Type*} [Group D]
    [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) D E) : Prop :=
  ∃ e : D ≃* A6,
    (∃ c : E ≃ₗ[ZMod 2] Vector, ∀ a v, c (σ a v) = action (e a) (c v)) ∨
    (∃ c : E ≃ₗ[ZMod 2] (Vector × Vector),
      ∀ a v, c (σ a v) = (action.prod action) (e a) (c v))

/-- Changing the independently chosen A₆ marking preserves naturality. -/
theorem natural_of_coordinates {D E : Type*} [Group D]
    [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) D E) (hσ : HasNaturalCoordinates σ)
    (e : D ≃* A6) (α : MulAut D) (u : E ≃ₗ[ZMod 2] E)
    (hu : ∀ a v, u (σ a v) = σ (α a) (u v)) : MulAut.congr e α ∈ natural := by
  obtain ⟨f, hf⟩ := hσ
  have hn : MulAut.congr f α ∈ natural := by
    rcases hf with ⟨c,hc⟩ | ⟨c,hc⟩
    · apply natural_of_intertwiner (MulAut.congr f α) (c.symm.trans (u.trans c))
      intro a v
      have hh := hc (f.symm a) (c.symm v)
      rw [f.apply_symm_apply, c.apply_symm_apply] at hh
      change c (u (c.symm (action a v))) =
        action (f (α (f.symm a))) (c (u (c.symm v)))
      rw [← hh, c.symm_apply_apply, hu, hc]
    · apply natural_of_pair_intertwiner (MulAut.congr f α) (c.symm.trans (u.trans c))
      intro a v
      have hh := hc (f.symm a) (c.symm v)
      rw [f.apply_symm_apply, c.apply_symm_apply] at hh
      change c (u (c.symm ((action.prod action) a v))) =
        (action.prod action) (f (α (f.symm a))) (c (u (c.symm v)))
      rw [← hh, c.symm_apply_apply, hu, hc]
  have he : MulAut.congr e α =
      (f.symm.trans e) * MulAut.congr f α * (f.symm.trans e)⁻¹ := by
    apply MulEquiv.ext
    intro a
    change e (α (e.symm a)) = e (f.symm (f (α (f.symm (f (e.symm a))))))
    simp only [f.symm_apply_apply]
  rw [he]
  exact (natural_conjugation_iff _ _).mpr hn

/-- Restricting the natural tensor to A₆ gives its two actual natural copies.
The second tensor factor also restricts to the natural Z₃-module. -/
theorem tensor_hasNaturalCoordinates :
    HasNaturalCoordinates
      ((BinaryPermutation.ThreeTensor.action action).comp
        (MonoidHom.inl A6 (Equiv.Perm (Fin 3)))) := by
  refine ⟨MulEquiv.refl A6, Or.inr ⟨BinaryPermutation.ThreeTensor.pairEquiv, ?_⟩⟩
  intro a v
  exact BinaryPermutation.ThreeTensor.pairEquiv_equivariant action a v

end Representation.BinaryAlternatingSixNaturalNormalizer
