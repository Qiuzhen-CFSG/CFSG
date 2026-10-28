module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic

/-!
# Nondegenerate planes inside nonisotropic subspaces

A nonzero value of an alternating form supplies a nondegenerate plane.
An isotropic subspace lies in its own orthogonal complement, hence has at
most half the dimension of a finite nondegenerate space. These elementary
linear facts are used in Aschbacher–Smith, Lemma 13.3.12(2), printed p.890.
-/

public section
open Module Submodule
namespace LinearMap.BilinForm
variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- A pair with nonzero pairing spans a nondegenerate plane. -/
theorem span_pair_nondegenerate_of_pairing_ne_zero
    (B : LinearMap.BilinForm K W) (ha : B.IsAlt) (x y : W) (hxy : B x y≠0) :
    finrank K (span K {x,y})=2 ∧ (B.restrict (span K {x,y})).Nondegenerate := by
  have hyx : B y x≠0 := fun h => hxy ((ha.eq_iff).mpr h)
  have hli : LinearIndependent K ![x,y] := by
    rw [linearIndependent_fin2]
    constructor
    · intro hy
      change y=0 at hy
      exact hxy (by rw [hy]; simp)
    · intro a he
      have h := congrArg (fun w => B w y) he
      exact hxy (by simpa [ha.self_eq_zero] using h.symm)
  have hdim : finrank K (span K {x,y})=2 := by
    have hr : Set.range ![x,y] = ({x,y} : Set W) := by
      ext z
      simp [or_comm]
    rw [← hr]
    exact finrank_span_eq_card hli
  refine ⟨hdim,B.nondegenerate_restrict_of_disjoint_orthogonal ha.isRefl ?_⟩
  rw [disjoint_def]
  intro v hv ho
  obtain ⟨a,b,rfl⟩ := mem_span_pair.mp hv
  have hx := ho x (subset_span (by simp : x∈({x,y}:Set W)))
  have hy := ho y (subset_span (by simp : y∈({x,y}:Set W)))
  have hb : b=0 := by
    have hh : b*B x y=0 := by simpa [map_add,map_smul,ha.self_eq_zero] using hx
    exact (mul_eq_zero.mp hh).resolve_right hxy
  have ha0 : a=0 := by
    have hh : a*B y x=0 := by simpa [map_add,map_smul,ha.self_eq_zero] using hy
    exact (mul_eq_zero.mp hh).resolve_right hyx
  simp [ha0,hb]

/-- Every nonisotropic subspace contains a nondegenerate plane. -/
theorem exists_nondegenerate_plane_of_not_isotropic
    (B : LinearMap.BilinForm K W) (ha : B.IsAlt) (U : Submodule K W)
    (hU : ¬∀x∈U,∀y∈U,B x y=0) :
    ∃P : Submodule K W,P≤U ∧ finrank K P=2 ∧ (B.restrict P).Nondegenerate := by
  push Not at hU
  obtain ⟨x,hx,y,hy,hxy⟩ := hU
  exact ⟨span K {x,y},span_le.mpr (by intro z hz; rcases (show z=x ∨ z=y by simpa using hz) with rfl | rfl <;> assumption),
    span_pair_nondegenerate_of_pairing_ne_zero B ha x y hxy⟩

/-- An isotropic subspace has at most half the ambient dimension. -/
theorem twice_finrank_le_of_isotropic [FiniteDimensional K W]
    (B : LinearMap.BilinForm K W) (hn : B.Nondegenerate) (U : Submodule K W)
    (hU : ∀x∈U,∀y∈U,B x y=0) : 2*finrank K U≤finrank K W := by
  have hle : U≤B.orthogonal U := fun x hx y hy => hU y hy x hx
  have hd := finrank_mono hle
  rw [B.finrank_orthogonal hn] at hd
  omega
end LinearMap.BilinForm
