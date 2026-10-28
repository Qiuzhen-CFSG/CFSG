module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex.Normalization
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex.Rigidity
public import Theory.SpecificGroups.Suzuki.FieldTorus

/-!
# Pointwise torus fixers in the Suzuki automorphism group

An automorphism preserving the standard root group and fixing the split torus
pointwise is inner by a torus element. The Weyl normalization adjusts it by a
torus conjugation; coordinate rigidity then identifies the adjusted automorphism
with an entrywise field automorphism. Pointwise fixation of the torus detects
that field automorphism as the identity.

This is the intrinsic automorphism calculation for GLS, Volume 4, Chapter 4,
Lemma 3.2(e), `refs/KGroup/GLS4/Chapter4.tex`, lines 360–373. Its marked ambient
application is in the parent ModelCentralizer module.
-/

noncomputable section
namespace BenderSuzuki.MatrixGroups
open Subgroup
open scoped IsMulCommutative

/-- A root-preserving automorphism fixing the split torus pointwise is
conjugation by an element of that same torus. -/
public theorem suzukiAut_eq_torus_conj_of_root_preserving_torus_fixed (m : ℕ) (hm : 1 ≤ m)
    (α : MulAut (SuzukiMatrixGroup m))
    (hU : (SuzukiRootSubgroup m).map α.toMonoidHom = SuzukiRootSubgroup m)
    (hfix : ∀ x ∈ SuzukiSplitTorus m, α x = x) :
    ∃ s : SuzukiSplitTorus m, α = MulAut.conj (s : SuzukiMatrixGroup m) := by
  have hT : (SuzukiSplitTorus m).map α.toMonoidHom = SuzukiSplitTorus m := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change α y ∈ SuzukiSplitTorus m
      rw [hfix y hy]
      exact hy
    · intro hx
      exact ⟨x, hx, hfix x hx⟩
  obtain ⟨s, hsU, hsT, hsw⟩ := suzukiAut_normalize_weyl m hm α hU hT
  obtain ⟨σ, hσ⟩ := suzukiAut_eq_fieldAut_of_normalized m hm _ hsU hsT hsw
  have hfield (x : SuzukiMatrixGroup m) (hx : x ∈ SuzukiSplitTorus m) :
      suzukiFieldAut m σ x = x := by
    rw [← hσ, MulAut.mul_apply, hfix x hx, MulAut.conj_apply]
    let := suzukiSplitTorus_isCyclic m hm
    have hc := congrArg Subtype.val (mul_comm s (⟨x, hx⟩ : SuzukiSplitTorus m))
    change (s : SuzukiMatrixGroup m) * x = x * s at hc
    rw [hc, mul_inv_cancel_right]
  have hσ1 : σ = 1 := field_eq_one_of_torus_two_power m hm σ (by
    intro u
    exact ⟨0, by rw [hfield _ (splitTorusElement_mem m u), mul_inv_cancel, one_pow]⟩)
  have hβ : MulAut.conj (s : SuzukiMatrixGroup m) * α = 1 := by
    rw [hσ, hσ1, ← suzukiFieldAutHom_apply, map_one]
  refine ⟨s⁻¹, ?_⟩
  change α = MulAut.conj ((s : SuzukiMatrixGroup m)⁻¹)
  rw [map_inv]
  exact eq_inv_of_mul_eq_one_right hβ
end BenderSuzuki.MatrixGroups
