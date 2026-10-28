module

public import Theory.Representation.BinaryPermutation.FiveTensorLowRank
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five
public import Theory.Representation.BinaryPermutation.FiveGeometry

/-!
# Singular tensor coordinates for Sylow-fixed vectors

The regular Klein four on the first four letters fixes precisely the
weight-four line in the five-point augmentation core. The pair coordinates
of the tensor product with the three-point core therefore have the same
first tensor factor. Enlarge this Klein four to a Sylow subgroup and
conjugate to an arbitrary Sylow subgroup of S₅ × S₃. The actual permutation
transport preserves weight, hence singularity of the first factor.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma 14.4.6(a), printed p.1008. The action and factor order are those of
`FiveTensorLowRank.Space` and `FiveTensorLowRank.action`.
-/

public section

open TensorProduct
namespace BinaryPermutation.FiveTensorFixedLine
open FiveTensorLowRank
open CubicFixedSpace.Five

private def weightFour : core (Fin 5) :=
  ⟨![1,1,1,1,0], by rw [mem_core]; decide⟩

private theorem weightFour_singular : FiveGeometry.form weightFour = 0 := by decide

private theorem fixed_core (v : core (Fin 5))
    (h₁ : coreRepresentation (Fin 5) first.val v = v)
    (h₂ : coreRepresentation (Fin 5) second.val v = v) :
    v = v.val 0 • weightFour := by
  have h : ∀ x : Full (Fin 5), (∑ i, x i) = 0 →
      representation (Fin 5) first.val x = x →
      representation (Fin 5) second.val x = x →
      x = x 0 • ![1,1,1,1,0] := by decide
  exact Subtype.ext (h v.val v.property (congrArg Subtype.val h₁) (congrArg Subtype.val h₂))

private theorem fixed_tensor (z : Space)
    (h₁ : action (first.val, 1) z = z)
    (h₂ : action (second.val, 1) z = z) :
    ∃ w : core (Fin 3), z = weightFour ⊗ₜ[ZMod 2] w := by
  let p := ThreeTensor.pairEquiv z
  have hfirst := congrArg ThreeTensor.pairEquiv h₁
  have hsecond := congrArg ThreeTensor.pairEquiv h₂
  change ThreeTensor.pairEquiv (ThreeTensor.action (coreRepresentation (Fin 5))
    (first.val, 1) z) = _ at hfirst
  change ThreeTensor.pairEquiv (ThreeTensor.action (coreRepresentation (Fin 5))
    (second.val, 1) z) = _ at hsecond
  rw [ThreeTensor.pairEquiv_equivariant] at hfirst hsecond
  have hp₁ := fixed_core p.1 (congrArg Prod.fst hfirst) (congrArg Prod.fst hsecond)
  have hp₂ := fixed_core p.2 (congrArg Prod.snd hfirst) (congrArg Prod.snd hsecond)
  let w : core (Fin 3) := ⟨![p.1.val 0, p.2.val 0, -p.1.val 0 - p.2.val 0], by
    rw [mem_core, Fin.sum_univ_three]
    change p.1.val 0 + p.2.val 0 + (-p.1.val 0 - p.2.val 0) = 0
    ring⟩
  refine ⟨w, ThreeTensor.pairEquiv.injective ?_⟩
  rw [ThreeTensor.pairEquiv_tmul]
  exact Prod.ext hp₁ hp₂

/-- Actual permutation transport preserves singularity in the five-point core. -/
theorem singular_permute (g : Equiv.Perm (Fin 5)) (u : core (Fin 5))
    (hu : FiveGeometry.form u = 0) :
    FiveGeometry.form (coreRepresentation (Fin 5) g u) = 0 := by
  rw [FiveGeometry.singular_iff] at hu ⊢
  rcases hu with rfl | hu
  · exact Or.inl (map_zero _)
  right
  rw [← hu]
  apply Finset.card_bij (fun i _ => g.symm i)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ hij
    exact g.symm.injective hij
  · intro j hj
    refine ⟨g j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, g.symm_apply_apply j⟩
    change u.val (g.symm (g j)) ≠ 0
    rw [g.symm_apply_apply]
    exact (Finset.mem_filter.mp hj).2

/-- Every nonzero vector fixed by an arbitrary Sylow two-subgroup has
nonzero pure tensor coordinates with a singular first factor. -/
theorem sylow_fixed_coordinates
    (P : Sylow 2 (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)))
    (z : Space) (hz : z ≠ 0) (hfix : ∀ g ∈ P, action g z = z) :
    ∃ u : core (Fin 5), ∃ w : core (Fin 3),
      u ≠ 0 ∧ w ≠ 0 ∧ FiveGeometry.form u = 0 ∧ z = u ⊗ₜ[ZMod 2] w := by
  let ι : alternatingGroup (Fin 5) →*
      Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3) :=
    (MonoidHom.inl _ _).comp (alternatingGroup (Fin 5)).subtype
  obtain ⟨Q, hKQ⟩ := (klein_isPGroup.map ι).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)) Q P
  have hP : (Q : Subgroup _).map (MulAut.conj g).toMonoidHom = (P : Subgroup _) := by
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have hinv (x : Space) : action g⁻¹ (action g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hginv (x : Space) : action g (action g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hK (a : alternatingGroup (Fin 5)) (ha : a ∈ klein) :
      action (ι a) (action g⁻¹ z) = action g⁻¹ z := by
    have hm : g * ι a * g⁻¹ ∈ (P : Subgroup _) := by
      rw [← hP]
      exact ⟨ι a, hKQ (Subgroup.mem_map_of_mem ι ha), rfl⟩
    have hh := congrArg (action g⁻¹) (hfix _ hm)
    simpa only [map_mul, Module.End.mul_apply, hinv] using hh
  obtain ⟨w, hw⟩ := fixed_tensor (action g⁻¹ z) (hK first first_mem) (hK second second_mem)
  have he : z = coreRepresentation (Fin 5) g.1 weightFour ⊗ₜ[ZMod 2]
      coreRepresentation (Fin 3) g.2 w := by
    rw [← hginv z, hw]
    rfl
  refine ⟨_, _, ?_, ?_, singular_permute g.1 weightFour weightFour_singular, he⟩
  · intro h
    rw [h, zero_tmul] at he
    exact hz he
  · intro h
    rw [h, tmul_zero] at he
    exact hz he
end BinaryPermutation.FiveTensorFixedLine
