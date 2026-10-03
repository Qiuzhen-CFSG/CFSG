module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.PGroup

/-!
# Projecting elementary subgroups of a commuting product

If a prime-group `A` commutes with a supplement `C`, the projection to `C`
of the inverse image of an elementary subgroup under multiplication is a
prime-group. Its elements have their `p`th powers in `A ∩ C`.

The kernel of multiplication injects into `A`. Pulling back the elementary
subgroup therefore gives an extension of prime-groups, and projection
preserves the prime-group property. The power assertion follows by taking
the `p`th power of a product of commuting elements.

This intrinsic reduction avoids choosing Sylow conjugators in the binary
centralizer argument following GLS, Number 2, Proposition 22.4.
-/

namespace Subgroup

/-- The factor projection of an elementary subgroup is a prime-group whose
`p`th powers belong to the overlap of the commuting factors. -/
public theorem exists_pSubgroup_projection_of_elementary
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (A C B : Subgroup G) (hA : IsPGroup p A)
    (hcomm : ∀ a : A, ∀ c : C, Commute (a : G) (c : G))
    (hB : B ≤ A ⊔ C) [IsElementaryAbelian p B] :
    ∃ T : Subgroup C, IsPGroup p T ∧ B ≤ A ⊔ T.map C.subtype ∧
      ∀ t : T, ((t : C) : G) ^ p ∈ A := by
  let f : A × C →* G := A.subtype.noncommCoprod C.subtype hcomm
  have hfrange : f.range = A ⊔ C := by
    exact (MonoidHom.noncommCoprod_range _ _ _).trans
      (by rw [A.range_subtype, C.range_subtype])
  let k : f.ker →* A := (MonoidHom.fst A C).comp f.ker.subtype
  have hk : Function.Injective k := by
    intro x y hxy
    have hfst : x.val.1 = y.val.1 := hxy
    have hx : (x.val.1 : G) * (x.val.2 : G) = 1 := x.property
    have hy : (y.val.1 : G) * (y.val.2 : G) = 1 := y.property
    have hsnd : x.val.2 = y.val.2 := by
      apply Subtype.ext
      apply mul_left_cancel (a := (x.val.1 : G))
      exact hx.trans (by simpa only [hfst] using hy.symm)
    exact Subtype.ext (Prod.ext hfst hsnd)
  have hker : IsPGroup p f.ker := hA.of_injective k hk
  let W : Subgroup (A × C) := B.comap f
  have hW : IsPGroup p W :=
    (IsElementaryAbelian.isPGroup p B).comap_of_ker_isPGroup f hker
  let T : Subgroup C := W.map (MonoidHom.snd A C)
  refine ⟨T, hW.map _, ?_, ?_⟩
  · intro b hb
    obtain ⟨x, hx⟩ := (show b ∈ f.range from hfrange.symm ▸ hB hb)
    have hxW : x ∈ W := by
      change f x ∈ B
      rwa [hx]
    have hxT : x.2 ∈ T := ⟨x, hxW, rfl⟩
    rw [← hx]
    exact mul_mem_sup x.1.property (show (x.2 : G) ∈ T.map C.subtype from
      ⟨x.2, hxT, rfl⟩)
  · intro t
    obtain ⟨x, hxW, hxt⟩ := t.property
    have hpow : ((x.1 : G) * (x.2 : G)) ^ p = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (p := p) (f x) hxW
    rw [(hcomm x.1 x.2).mul_pow] at hpow
    have heq : (x.2 : G) ^ p = ((x.1 : G) ^ p)⁻¹ :=
      eq_inv_of_mul_eq_one_right hpow
    have ht : (t : C) = x.2 := hxt.symm
    rw [ht, heq]
    exact A.inv_mem (A.pow_mem x.1.property p)

end Subgroup
