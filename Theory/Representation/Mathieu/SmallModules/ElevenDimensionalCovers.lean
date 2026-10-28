module
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.CentralCover
public import Theory.Representation.Mathieu.SmallModules.M22Recognition
public import Theory.Mathieu.M12.Properties.AutCover
public import Theory.Mathieu.M22.BinaryCovers
public import Theory.Representation.Mathieu.M22James.MinimumDegree

/-!
# Small faithful binary representations of Mathieu central covers

A faithful irreducible representation of degree at most eleven with central
quotient M₁₂ is its native permutation heart. In the M₂₂ case, the full
cover theorem leaves the simple or triple cover; James's minimum degree
twelve excludes the latter. Native recognition then gives the Todd module
or its code dual. Both results construct group isomorphisms and equivariant
linear equivalences on the original representation.

These are the small-module comparisons used in the J₄ pushing-up branch of
Aschbacher–Smith 4.2.13, printed pp.611–612. The recognition and covering
proofs, including their James/ATLAS source attribution, are in the imports.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Representation Representation.MathieuSmall Sporadic.Mathieu

namespace Representation.MathieuSmall
variable {L V : Type*} [Group L] [AddCommGroup V] [Module (ZMod 2) V]

/-- A native M₁₂ marking identifies the full acting group, including its center. -/
theorem IsM12Heart.center_eq_bot {σ : Representation (ZMod 2) L V}
    (h : IsM12Heart σ) : center L = ⊥ := by
  obtain ⟨e, _⟩ := h
  apply card_eq_one.mp
  exact (Nat.card_congr (centerCongr e).toEquiv).trans
    (by rw [m12_center_eq_bot]; exact card_bot)

/-- Either native M₂₂ marking identifies the full acting group. -/
theorem IsM22ToddOrDual.center_eq_bot {σ : Representation (ZMod 2) L V}
    (h : IsM22ToddOrDual σ) : center L = ⊥ := by
  obtain ⟨e, _⟩ := h
  apply card_eq_one.mp
  exact (Nat.card_congr (centerCongr e).toEquiv).trans
    (by rw [m22_center_eq_bot]; exact card_bot)

variable [Finite L] [IsQuasisimple L] [FiniteDimensional (ZMod 2) V]

theorem m12_of_finrank_le_eleven (σ : Representation (ZMod 2) L V)
    (hf : Function.Injective σ) [σ.IsIrreducible]
    (e : (L ⧸ center L) ≃* M12) (hd : Module.finrank (ZMod 2) V ≤ 11) :
    IsM12Heart σ := by
  let f := M12Recognition.CentralCover.groupEquiv σ hf inferInstance e
  let τ : Representation (ZMod 2) M12 V := σ.comp f.symm.toMonoidHom
  let : τ.IsIrreducible :=
    (irreducible_comp_surjective_iff f.symm.toMonoidHom f.symm.surjective σ).mpr inferInstance
  have hb := M12DegreeGap.finrank_le_ten τ
    (hf.comp f.symm.injective) (hd.trans (by decide))
  exact ⟨f,M12Recognition.CentralCover.equiv_heart_of_finrank_le_ten σ hf inferInstance e hb⟩

theorem m22_of_finrank_le_eleven (σ : Representation (ZMod 2) L V)
    (hf : Function.Injective σ) [σ.IsIrreducible]
    (e : (L ⧸ center L) ≃* M22) (hd : Module.finrank (ZMod 2) V ≤ 11) :
    IsM22ToddOrDual σ := by
  rcases M22BinaryCovers.simple_or_triple_of_binary_irreducible σ hf e with hs | ht
  · obtain ⟨f⟩ := hs
    let τ : Representation (ZMod 2) M22 V := σ.comp f.symm.toMonoidHom
    let : τ.IsIrreducible :=
      (irreducible_comp_surjective_iff f.symm.toMonoidHom f.symm.surjective σ).mpr inferInstance
    obtain ⟨b,hb | hb⟩ := M22Recognition.of_small_degree τ
      (hf.comp f.symm.injective) (hd.trans (by decide))
    · obtain ⟨E⟩ := hb
      refine ⟨f.trans b,.inl ⟨{ toLinearEquiv := E.toLinearEquiv, isIntertwining' := ?_ }⟩⟩
      intro l
      simpa only [τ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply,MulEquiv.trans_apply]
        using E.isIntertwining' (f l)
    · obtain ⟨E⟩ := hb
      refine ⟨f.trans b,.inr ⟨{ toLinearEquiv := E.toLinearEquiv, isIntertwining' := ?_ }⟩⟩
      intro l
      simpa only [τ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply,MulEquiv.trans_apply]
        using E.isIntertwining' (f l)
  · obtain ⟨f⟩ := ht
    let τ : Representation (ZMod 2) M22TripleCover V := σ.comp f.symm.toMonoidHom
    let : τ.IsIrreducible :=
      (irreducible_comp_surjective_iff f.symm.toMonoidHom f.symm.surjective σ).mpr inferInstance
    have hb := M22TripleCover.faithful_irreducible_finrank_ge_twelve
      τ (hf.comp f.symm.injective)
    omega
end Representation.MathieuSmall
