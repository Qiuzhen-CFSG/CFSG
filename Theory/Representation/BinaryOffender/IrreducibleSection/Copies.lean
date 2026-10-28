module
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport
public import Theory.Representation.Quotient
public import Mathlib.RepresentationTheory.Irreducible

/-!
# An Irr⁺ section inside copies of one simple module

Choose a nonzero coordinate of the embedded section. Its projection is onto
by irreducibility of the model. The kernel is a proper invariant subspace,
so the Irr⁺ condition makes it fixed. The model has no fixed vectors, hence
neither does the embedded section; the coordinate projection is injective.
Thus the original section is one copy, with its specified acting-group map.

The actual source application restricts the A₅ module sum from the rank-one
reduction to a chosen member of Irr⁺ in Aschbacher--Smith 12.2.2(3d), p.795.
No semisimplicity or splitting of the original section is assumed.
-/

public noncomputable section
open Representation Subgroup
namespace Representation.BinaryOffender
variable {G V A W ι : Type*} [Group G] [Group A]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V)

set_option backward.isDefEq.respectTransparency false in
/-- A specified embedding into copies of a fixed-free simple model identifies
the original Irr⁺ section with that model. -/
theorem IsIrrPlus.linearEquiv_of_embedding_copies {X : Subgroup G}
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ X I)
    (σ : Representation (ZMod 2) A W) (hi : IsIrreducible σ)
    (hfix : ∀ w, (∀ a, σ a w = w) → w = 0)
    (f : X →* A) (hf : Function.Surjective f)
    (E : I →ₗ[ZMod 2] (ι → W)) (hE : Function.Injective E)
    (hact : ∀ (x : X) (v : I) i,
      E ((invariantSubspace ρ X I hI.choose).toRepresentation x v) i =
        σ (f x) (E v i)) :
    ∃ e : I ≃ₗ[ZMod 2] W, ∀ (x : X) (v : I),
      e ((invariantSubspace ρ X I hI.choose).toRepresentation x v) =
        σ (f x) (e v) := by
  classical
  let τ := (invariantSubspace ρ X I hI.choose).toRepresentation
  let : IsIrreducible (σ.comp f) := (irreducible_comp_surjective_iff f hf σ).mpr hi
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hI.ne_bot ρ)
  let v' : I := ⟨v, hv⟩
  have he0 : E v' ≠ 0 := by
    intro he
    have hh := hE (he.trans E.map_zero.symm)
    exact hv0 (congrArg Subtype.val hh)
  obtain ⟨i, hi0⟩ : ∃ i, E v' i ≠ 0 := by
    by_contra h
    apply he0
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  let p : τ.IntertwiningMap (σ.comp f) := {
    toLinearMap := (LinearMap.proj i).comp E
    isIntertwining' := fun x => by
      apply LinearMap.ext
      intro w
      exact hact x w i }
  have hp0 : p ≠ 0 := by
    intro he
    exact hi0 (DFunLike.congr_fun he v')
  have hsurj : Function.Surjective p :=
    (IsIrreducible.surjective_or_eq_zero p).resolve_right hp0
  let J := p.toLinearMap.ker.map I.subtype
  have hJI : J ≤ I := Submodule.map_subtype_le _ _
  have hJ : X ≤ subspaceStabilizer ρ J := by
    apply le_subspaceStabilizer
    rintro x hx _ ⟨w, hw, rfl⟩
    refine ⟨τ ⟨x, hx⟩ w, ?_, rfl⟩
    change p (τ ⟨x, hx⟩ w) = 0
    rw [p.isIntertwining]
    change σ (f ⟨x, hx⟩) (p w) = 0
    rw [show p w = 0 from hw, map_zero]
  have hcentral : J ≤ fixedSpace ρ X := by
    apply (hI.eq_or_le_fixedSpace ρ hJ hJI).resolve_left
    intro he
    apply hi0
    obtain ⟨w, hw, hwv⟩ := he.symm ▸ hv
    have hwe : w = v' := Subtype.ext hwv
    exact hwe ▸ hw
  have hinj : Function.Injective p := by
    apply (injective_iff_map_eq_zero p.toLinearMap).mpr
    intro w hw
    have hz : w.val ∈ fixedSpace ρ X := hcentral ⟨w, hw, rfl⟩
    apply hE
    rw [map_zero]
    funext j
    apply hfix
    intro a
    obtain ⟨x, rfl⟩ := hf a
    have hx : τ x w = w := Subtype.ext (hz x)
    exact (hact x w j).symm.trans (congrArg (fun w => E w j) hx)
  exact ⟨LinearEquiv.ofBijective p.toLinearMap ⟨hinj, hsurj⟩,
    fun x v => hact x v i⟩

end Representation.BinaryOffender
