module
public import Theory.Representation.PSL3Two.FanoLineMoved

/-!
# Whole Fano quotients with trivial fixed space

The constant vector in a Fano permutation module has fixed image under any
intertwiner. If the target has no fixed vectors, that image vanishes, so the
augmentation core already surjects onto the whole target. The checked core
classification then identifies the entire representation as the dual natural
module or the six-dimensional line core, and proves full commutator generation.

The original subgroup application is FixedCoreSource/Amalgam/LinearFixedFree.
Source: Aschbacher–Smith H.5.3, printed pp.385–386, used in 13.4.7, p.901.
-/

public noncomputable section
open Representation Module
namespace BinaryLinearThree.FanoFixedFreeQuotient
open FanoDecomposition FanoLineQuotients FanoLineMoved Representation.BinaryOffender
variable {A M : Type*} [_root_.Group A] [AddCommGroup M] [Module (ZMod 2) M]

/-- If a Fano quotient has no fixed vectors, its entire module is the
augmentation-core image, with the actual dual-natural or core action. -/
theorem whole_models (f : A →* Group) (hf : Function.Surjective f)
    (ρ : Representation (ZMod 2) A M)
    (q : Representation.IntertwiningMap (lineRepresentation.comp f) ρ)
    (hq : Function.Surjective q) (hd : 1 < finrank (ZMod 2) M)
    (hfixed : ∀ m : M, (∀ a : A, ρ a m = m) → m = 0) :
    Function.Surjective (coreMap f ρ q) ∧
      subspaceCommutator ρ ⊤ ⊤ = ⊤ ∧
      (Nonempty (Representation.Equiv (W.dual.comp f) ρ) ∨
        Nonempty (Representation.Equiv (lineCoreRepresentation.comp f) ρ)) ∧
      (finrank (ZMod 2) M = 3 ∨ finrank (ZMod 2) M = 6) := by
  have hconst : q (BinaryPermutation.allOne Line) = 0 := hfixed _ (by
    intro a
    rw [← q.isIntertwining]
    rfl)
  have hsurj : Function.Surjective (coreMap f ρ q) := by
    intro m
    obtain ⟨v,rfl⟩ := hq m
    refine ⟨projection v, ?_⟩
    change q (inclusion (projection v)) = q v
    have he := congrArg q (decomposition v)
    simpa only [map_add,map_smul,hconst,smul_zero,add_zero] using he
  have hr : (coreMap f ρ q).range.toSubmodule = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hm : subspaceCommutator ρ ⊤ ⊤ = ⊤ :=
    (core_image_eq_moved f hf ρ q hq).symm.trans hr
  let R := (coreMap f ρ q).range
  let j : R.toRepresentation.IntertwiningMap ρ := {
    toLinearMap := R.toSubmodule.subtype
    isIntertwining' a := rfl }
  have hj : Function.Bijective j := ⟨Subtype.val_injective, by
    intro m
    exact ⟨⟨m,hr ▸ Submodule.mem_top⟩,rfl⟩⟩
  have hmodels : Nonempty (Representation.Equiv (W.dual.comp f) ρ) ∨
      Nonempty (Representation.Equiv (lineCoreRepresentation.comp f) ρ) := by
    rcases FanoLineMoved.core_image_models f hf ρ q hq hd with he | he
    · obtain ⟨e⟩ := he
      exact Or.inl ⟨e.trans (j.ofBijective hj)⟩
    · obtain ⟨e⟩ := he
      exact Or.inr ⟨e.trans (j.ofBijective hj)⟩
  have hdim := moved_dimension f hf ρ q hq hd
  rw [hm,finrank_top] at hdim
  exact ⟨hsurj,hm,hmodels,hdim⟩
end BinaryLinearThree.FanoFixedFreeQuotient
