module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.Centralizers.Linear
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.OrthogonalPair.ModuleRecognition

/-!
# Centralizers on the actual binary orthogonal four-space

For a dihedral pair whose two rotations have no nonzero fixed vectors,
every nonzero invariant subspace contains a common reflection-fixed vector.
Its four rotation-orbit vectors are independent, so the subspace has
dimension at least four. A commuting involution therefore fixes the whole
four-space.

The natural-action theorem uses the actual Siegel-generated elementary
orthogonal carrier. Its proved `pairEquiv` supplies the group coordinates;
the two rotation fixed-space calculations are checked on the concrete
sixteen-vector module. This is the orthogonal case in Aschbacher--Smith
G.9.2, printed pp.352--353.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality

open DihedralGroup ClassicalOrthogonal.BinaryD2

universe v

variable {G : Type*} [Group G] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

theorem pair_involution_centralizer [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) Pair W)
    (hd : Module.finrank (ZMod 2) W = 4)
    (hr : ∀ w, σ (r 1, 1) w = w → w = 0)
    (hs : ∀ w, σ (1, r 1) w = w → w = 0)
    (t : Module.End (ZMod 2) W) (ht : t*t=1) (hc : ∀ g, Commute t (σ g)) : t=1 := by
  apply involution_eq_one_of_subspace_bound σ _ t ht hc
  intro U hU hstable
  let τ := σ.subrepresentation U hstable
  let : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU
  obtain ⟨w, hw, ha, hb⟩ := exists_common_fixed τ
  have hτr (w : U) (h : τ (r 1, 1) w = w) : w = 0 :=
    Subtype.ext (hr w (congrArg Subtype.val h))
  have hτs (w : U) (h : τ (1, r 1) w = w) : w = 0 :=
    Subtype.ext (hs w (congrArg Subtype.val h))
  have hh := LinearMap.finrank_le_finrank_of_injective
    (orbitMap_injective τ w hw ha hb hτr hτs)
  rw [hd]
  simpa [Space, ClassicalOrthogonal.VectorD, ClassicalOrthogonal.Index,
    Module.finrank_fintype_fun_eq_card] using hh

private theorem concrete_rotation_left_fixed_free : ∀ x : Space,
    (pairHom (r 1, 1)).val x = x → x = 0 := by decide +kernel

private theorem concrete_rotation_right_fixed_free : ∀ x : Space,
    (pairHom (1, r 1)).val x = x → x = 0 := by decide +kernel

theorem natural_omegaFour_involution_centralizer [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) G W) (e : G ≃* OmegaFour)
    (f : W ≃ₗ[ZMod 2] Space)
    (ha : ∀ g w, f (σ g w) = (e g).val.val (f w))
    (t : Module.End (ZMod 2) W) (ht : t*t=1) (hc : ∀ g, Commute t (σ g)) : t=1 := by
  let E := pairEquiv.trans e.symm
  let τ := σ.comp E.toMonoidHom
  have hd : Module.finrank (ZMod 2) W = 4 := by
    rw [f.finrank_eq]
    simp [Space, ClassicalOrthogonal.VectorD, ClassicalOrthogonal.Index,
      Module.finrank_fintype_fun_eq_card]
  apply pair_involution_centralizer τ hd _ _ t ht (fun g => hc (E g))
  · intro w hw
    apply f.injective
    rw [map_zero]
    apply concrete_rotation_left_fixed_free
    have hh := ha (E (r 1, 1)) w
    change f (τ (r 1, 1) w) = _ at hh
    rw [hw] at hh
    simpa [E] using hh.symm
  · intro w hw
    apply f.injective
    rw [map_zero]
    apply concrete_rotation_right_fixed_free
    have hh := ha (E (1, r 1)) w
    change f (τ (1, r 1) w) = _ at hh
    rw [hw] at hh
    simpa [E] using hh.symm

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality
