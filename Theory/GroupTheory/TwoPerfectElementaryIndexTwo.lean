module

public import Theory.GroupTheory.ElementaryIndexTwoNormalizer
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Two-perfect actions on elementary subgroups of index two

In a finite non-elementary group, the square of every automorphism fixes
an elementary abelian subgroup of index two. On its automorphism orbit,
therefore, every element of the action image squares to one. A two-perfect
acting group has trivial image in this two-group, and fixes the subgroup.

The ambient version uses the literal conjugation action of a normalizer.
It is the last normalizer argument in Aschbacher–Smith, combined manuscript
of 1 March 2004, proof of Theorem 12.6.2, printed p.828. It avoids choosing
an isomorphism with D₈ × E₆₄ or enumerating that group's elementary subgroups.
-/

public section

open Subgroup
open scoped Pointwise

namespace Subgroup

/-- A two-perfect group of automorphisms fixes every elementary abelian
index-two subgroup of a finite non-elementary group. -/
theorem twoPerfect_fixes_elementary_index_two {H R : Type*} [Group H] [Group R] [Finite R]
    (hH : IsPPerfect 2 H) (ρ : H →* MulAut R)
    (A : Subgroup R) (hA : IsElementaryAbelian 2 A) (hi : A.index = 2)
    (hR : ¬ IsElementaryAbelian 2 R) (h : H) : ρ h • A = A := by
  let : MulAction H (Subgroup R) := MulAction.compHom (Subgroup R) ρ
  let O := MulAction.orbit H A
  let f : H →* Equiv.Perm O := MulAction.toPermHom H O
  have hsq (g : H) : f g ^ 2 = 1 := by
    apply Equiv.ext
    intro B
    apply Subtype.ext
    obtain ⟨k, hk⟩ := B.property
    have hB : IsElementaryAbelian 2 B.val := by
      rw [← hk]
      let := hA
      exact IsElementaryAbelian.map (ρ k).toMonoidHom
    have hBi : B.val.index = 2 := by
      rw [← hk]
      exact (index_map_of_bijective (f := (ρ k).toMonoidHom) (ρ k).bijective A).trans hi
    change ρ g • (ρ g • B.val) = B.val
    rw [← mul_smul, ← pow_two]
    exact square_fixes_elementary_index_two B.val hB hBi hR (ρ g)
  have hp : IsPGroup 2 f.range := by
    intro x
    obtain ⟨g, hg⟩ := x.property
    refine ⟨1, ?_⟩
    apply Subtype.ext
    change x.val ^ (2 ^ 1) = 1
    simpa only [pow_one, ← hg] using hsq g
  have ht := hH.hom_eq_one_of_isPGroup hp f.rangeRestrict
  have he : f h = 1 := congrArg Subtype.val (DFunLike.congr_fun ht h)
  exact congrArg Subtype.val (DFunLike.congr_fun he ⟨A, MulAction.mem_orbit_self A⟩)

/-- Ambient conjugation version, with normality relative to the normalizer
of R rather than to the ambient group. -/
theorem twoPerfect_le_normalizer_elementary_index_two
    {G : Type*} [Group G] [Finite G] (K R Q : Subgroup G)
    (hK : IsPPerfect 2 K) (hKR : K ≤ normalizer (R : Set G))
    (hQR : Q ≤ R) (hQ : IsElementaryAbelian 2 Q)
    (hi : Q.relIndex R = 2) (hR : ¬ IsElementaryAbelian 2 R) :
    K ≤ normalizer (Q : Set G) := by
  let ρ : K →* MulAut R := R.normalizerMonoidHom.comp (inclusion hKR)
  let A := Q.subgroupOf R
  let := hQ
  have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hQR
  intro k hk
  have hfix := twoPerfect_fixes_elementary_index_two hK ρ A hA hi hR ⟨k, hk⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  have he := congrArg (fun B : Subgroup R => B.map R.subtype) hfix
  change (A.map (ρ ⟨k, hk⟩).toMonoidHom).map R.subtype = A.map R.subtype at he
  have hc : R.subtype.comp (ρ ⟨k, hk⟩).toMonoidHom =
      (MulAut.conj k).toMonoidHom.comp R.subtype := by
    ext x
    rfl
  rwa [map_map, hc, ← map_map, map_subgroupOf_eq_of_le hQR] at he

end Subgroup
