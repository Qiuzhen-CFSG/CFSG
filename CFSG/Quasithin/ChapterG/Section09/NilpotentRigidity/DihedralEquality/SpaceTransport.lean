module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.Restriction
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# The actual displacement summands after restriction

If the complementary space is fixed pointwise, the displacement span in a
subrepresentation is linearly equivalent to the ambient displacement span
by its inclusion. Consequently the ordinary factor alternatives, including
the natural orthogonal intertwiner, lift to the ambient module.

These are the summand identifications used when regrouping the factors in
Aschbacher--Smith G.9.2, printed p.353. Pointwise fixation of the complement
is a premise here; it must be proved by the equality induction.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The equivalence is the actual inclusion on underlying vectors. -/
@[expose] noncomputable def movedSpace_subrepresentation_equiv
    {W C : Submodule (ZMod 2) V} (hW : ∀ g, W ≤ W.comap (ρ g))
    (hsup : W ⊔ C = ⊤) (K : Subgroup G)
    (hC : ∀ g : K, ∀ v : C, ρ g v = (v : V)) :
    movedSpace (ρ.subrepresentation W hW) K ≃ₗ[ZMod 2] movedSpace ρ K :=
  (Submodule.equivMapOfInjective W.subtype W.injective_subtype _).trans
    (LinearEquiv.ofEq _ _
      (movedSpace_subrepresentation_map_of_fixed_complement ρ hW hsup K hC))

@[simp] theorem movedSpace_subrepresentation_equiv_apply
    {W C : Submodule (ZMod 2) V} (hW : ∀ g, W ≤ W.comap (ρ g))
    (hsup : W ⊔ C = ⊤) (K : Subgroup G)
    (hC : ∀ g : K, ∀ v : C, ρ g v = (v : V))
    (v : movedSpace (ρ.subrepresentation W hW) K) :
    (movedSpace_subrepresentation_equiv ρ hW hsup K hC v : V) = (v : W) := rfl

@[simp] theorem movedSpace_subrepresentation_equiv_symm_apply
    {W C : Submodule (ZMod 2) V} (hW : ∀ g, W ≤ W.comap (ρ g))
    (hsup : W ⊔ C = ⊤) (K : Subgroup G)
    (hC : ∀ g : K, ∀ v : C, ρ g v = (v : V))
    (v : movedSpace ρ K) :
    ((movedSpace_subrepresentation_equiv ρ hW hsup K hC).symm v : W) = (v : V) :=
  congrArg Subtype.val ((movedSpace_subrepresentation_equiv ρ hW hsup K hC).apply_symm_apply v)

theorem isNaturalOmegaFour_of_subrepresentation
    {W C : Submodule (ZMod 2) V} (hW : ∀ g, W ≤ W.comap (ρ g))
    (hsup : W ⊔ C = ⊤) (K : Subgroup G)
    (hC : ∀ g : K, ∀ v : C, ρ g v = (v : V))
    (h : IsNaturalOmegaFour (ρ.subrepresentation W hW) K
      (movedSpace (ρ.subrepresentation W hW) K)) :
    IsNaturalOmegaFour ρ K (movedSpace ρ K) := by
  obtain ⟨e, f, hf⟩ := h
  let E := movedSpace_subrepresentation_equiv ρ hW hsup K hC
  refine ⟨e, E.symm.trans f, ?_⟩
  intro g v
  have hh := congrArg Subtype.val (hf g (E.symm v))
  change ρ g ((E.symm v : W) : V) = _ at hh
  rw [movedSpace_subrepresentation_equiv_symm_apply] at hh
  exact hh

theorem isOrdinaryFactor_of_subrepresentation
    {W C : Submodule (ZMod 2) V} (hW : ∀ g, W ≤ W.comap (ρ g))
    (hsup : W ⊔ C = ⊤) (K : Subgroup G)
    (hC : ∀ g : K, ∀ v : C, ρ g v = (v : V))
    (h : IsOrdinaryFactor (ρ.subrepresentation W hW) K) :
    IsOrdinaryFactor ρ K := by
  have hd := (movedSpace_subrepresentation_equiv ρ hW hsup K hC).finrank_eq
  rcases h with ⟨he, hd'⟩ | ⟨he, hd'⟩
  · exact Or.inl ⟨he, hd ▸ hd'⟩
  · exact Or.inr ⟨isNaturalOmegaFour_of_subrepresentation ρ hW hsup K hC he, hd ▸ hd'⟩

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality
