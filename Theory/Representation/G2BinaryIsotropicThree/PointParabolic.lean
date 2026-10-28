module

public import Theory.Representation.G2BinaryIsotropicThree.Basic
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The full point stabilizer on the marked binary three-space

A three-dimensional linear equivalence fixing the first vector has an invertible
2×2 lower block. The actual opposite-pair SL₂ and two root translations realize
that block and the two upper coefficients. Multiplying by C(1), if necessary,
places the resulting element in G₂(2)′ without changing its three-space action.
Thus every point-fixing automorphism is realized in the actual derived group.

Source: Aschbacher–Smith 13.3.12(4), printed p.890, the final conjugator adjustment.
-/

@[expose] public section

open Atlas.SplitOctonion Module Submodule Subgroup Matrix
open scoped MatrixGroups
namespace Atlas.G2.Natural.BinaryIsotropicThree
open BinaryNondegeneratePlane Atlas.G2.Restricted.NaturalCoordinates
abbrev Three := Fin 3→K

theorem realize_point_fixed_equiv_full
    (A : Three≃ₗ[K]Three) (hA : A ![1,0,0]=![1,0,0]) :
    ∃g : Model K,∀v : Three,rho g (targetEmbed false v)=targetEmbed false (A v) := by
  let M : Matrix (Fin 3) (Fin 3) K := LinearMap.toMatrix' A.toLinearMap
  have hcol (i : Fin 3) : M i 0=![1,0,0] i := by
    change A (Pi.single 0 1) i=_
    have he : (Pi.single 0 (1:K) : Three)=![1,0,0] := by ext j;fin_cases j <;> simp
    rw [he,hA]
  have hinv : LinearMap.toMatrix' A.symm.toLinearMap*M=1 := by
    apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul,Matrix.toLin'_one,Matrix.toLin'_toMatrix',M]
    apply LinearMap.ext
    intro v
    exact A.symm_apply_apply v
  have hd : M.det≠0 := Matrix.det_ne_zero_of_left_inverse hinv
  let N : Matrix (Fin 2) (Fin 2) K := !![M 1 1,M 1 2;M 2 1,M 2 2]
  have he : N.det=M.det := by
    rw [Matrix.det_fin_two,Matrix.det_fin_three]
    simp [N,hcol]
  have hn : N.det=1 :=
    ((show ∀a : K,a=0∨a=1 by decide +kernel) N.det).resolve_left (he ▸ hd)
  let B : SL(2,K) := ⟨N,hn⟩
  let g := PairStabilizer.blockHom B*rootF (M 0 1)*rootD (M 0 2)
  refine ⟨g,?_⟩
  intro v
  have hAv : A v=M*ᵥv := (LinearMap.toMatrix'_mulVec A.toLinearMap v).symm
  rw [hAv]
  simp only [g,map_mul,Module.End.mul_apply]
  rw [firstHom_action B]
  ext i
  fin_cases i <;> simp [action_rootF,action_rootD,targetEmbed,B,N,
    Matrix.mulVec,dotProduct,Fin.sum_univ_three,hcol]
  all_goals ring

private theorem rootC_outside : rootC (1:K)∉commutator (Model K) := by
  intro h
  have hp : BinaryException.projection (rootC 1)=1 :=
    (QuotientGroup.eq_one_iff _).mpr (BinaryParabolicPair.commutator_eq_longRootClosure ▸ h)
  rw [BinaryException.project_C_eq_D,BinaryException.project_D_eq_F] at hp
  exact BinaryParabolicPair.quotientBit_ne_one hp

theorem realize_point_fixed_equiv_derived
    (A : Three≃ₗ[K]Three) (hA : A ![1,0,0]=![1,0,0]) :
    ∃g : commutator (Model K),∀v : Three,rho g.val (targetEmbed false v)=targetEmbed false (A v) := by
  obtain ⟨g,hg⟩ := realize_point_fixed_equiv_full A hA
  by_cases hd : g∈commutator (Model K)
  · exact ⟨⟨g,hd⟩,hg⟩
  · have hi : (commutator (Model K)).index=2 := by
      rw [BinaryParabolicPair.commutator_eq_longRootClosure,BinaryException.index_H]
    have hc : rootC (1:K)*g∈commutator (Model K) :=
      ((commutator (Model K)).mul_mem_iff_of_index_two hi).mpr (iff_of_false rootC_outside hd)
    refine ⟨⟨rootC 1*g,hc⟩,?_⟩
    intro v
    rw [map_mul,Module.End.mul_apply,hg]
    ext i
    fin_cases i <;> simp [targetEmbed,action_rootC]
end Atlas.G2.Natural.BinaryIsotropicThree
