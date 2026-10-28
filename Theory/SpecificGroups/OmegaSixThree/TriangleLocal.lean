module
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal.Action
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal.Reflections

/-!
# The concrete F.5 triangle stabilizer is S₄ × S₄

For each adjacent transposition in either four-line action, four equal-norm
reflections give a literal Omega element with that permutation and trivial
other factor. Each pair is already a proved commutator. These six witnesses
make the injective four-line action surjective. The resulting equivalence
retains the original triangle stabilizer embedding; the triangle-span factor
is first and the orthogonal-complement factor second.
Source: Aschbacher--Smith F.5.7, printed pp.302--303.
-/

@[expose] public section

namespace OmegaSixThree.TriangleLocal
open SixTernaryCoordinates OrthogonalityGraph

private def rootVector (side : Bool) (k : Fin 3) : Space :=
  if side then ![![0,0,1,1,0,0],![0,0,0,1,-1,0],![0,0,1,-1,0,0]] k
  else ![![1,0,0,0,0,0],![1,-1,0,0,0,1],![0,1,0,0,0,0]] k
private def otherBasis (side : Bool) (k : Fin 3) : Space :=
  if side then negativeBasis k else ![e 2,e 3,e 4] k
private def norm (side : Bool) : ZMod 3 := if side then -1 else 1
private theorem norm_sq (side : Bool) : (norm side)^2 = 1 := by cases side <;> decide
private theorem root_norm (side : Bool) (k : Fin 3) : quadratic (rootVector side k) = norm side := by
  revert side k; decide +kernel
private theorem other_norm (side : Bool) (k : Fin 3) : quadratic (otherBasis side k) = norm side := by
  revert side k; decide +kernel
private theorem root_orthogonal (side : Bool) (k : Fin 3) :
    pairing (rootVector side k) (otherBasis side 0) = 0 := by
  revert side k; decide +kernel
private theorem other_orthogonal (side : Bool) : pairing (otherBasis side 1) (otherBasis side 2) = 0 := by
  revert side; decide +kernel

private def rootReflection (side : Bool) (k : Fin 3) : LinearGroup :=
  reflection (norm side) (norm_sq side) (rootVector side k) (root_norm side k)
private def otherReflection (side : Bool) (k : Fin 3) : LinearGroup :=
  reflection (norm side) (norm_sq side) (otherBasis side k) (other_norm side k)

private def generator (side : Bool) (k : Fin 3) : omegaPlusSixThree :=
  ⟨(rootReflection side k * otherReflection side 0) *
      (otherReflection side 1 * otherReflection side 2),
    omegaPlusSixThree.mul_mem
      (reflection_pair_mem _ _ _ _ (root_norm side k) (other_norm side 0) (root_orthogonal side k))
      (reflection_pair_mem _ _ _ _ (other_norm side 1) (other_norm side 2) (other_orthogonal side))⟩

private theorem generator_triangle (side : Bool) (k : Fin 3) (i : Fin 3) :
    ∃ j : Fin 3, signed ((generator side k).val (negativeBasis i)) (negativeBasis j) := by
  have hh : ∀ (side : Bool) (k i : Fin 3),
      ∃ j : Fin 3, signed ((generator side k).val (negativeBasis i)) (negativeBasis j) := by
    unfold signed
    decide +kernel
  exact hh side k i

private theorem generator_mem (side : Bool) (k : Fin 3) : generator side k ∈ H := by
  apply (mem_triangleStabilizer_iff _).mpr
  have hm : Set.MapsTo (fun p : Point => generator side k • p) standardTriangle standardTriangle := by
    intro p hp
    obtain ⟨i,rfl⟩ := (mem_standardTriangle_iff p).mp hp
    obtain ⟨j,hj⟩ := generator_triangle side k i
    apply (mem_standardTriangle_iff _).mpr
    exact ⟨j, (point_eq_iff _ _ _ _).mpr hj⟩
  exact ((Set.Finite.injOn_iff_bijOn_of_mapsTo (by simp [standardTriangle]) hm).mp
    (MulAction.injective (generator side k)).injOn).image_eq

/-- An explicit Omega element realizing an adjacent transposition in either
four-line action, acting trivially in the other factor. -/
private def adjacentGenerator (side : Bool) (k : Fin 3) : H :=
  ⟨generator side k,generator_mem side k⟩

private theorem generator_action (side : Bool) (k : Fin 3) (other : Bool) (i : Fin 4) :
    signed ((generator side k).val (tetra other i))
      (tetra other ((if side = other then Equiv.swap k.castSucc k.succ else 1) i)) := by
  have hh : ∀ (side : Bool) (k : Fin 3) (other : Bool) (i : Fin 4),
      signed ((generator side k).val (tetra other i))
        (tetra other ((if side = other then Equiv.swap k.castSucc k.succ else 1) i)) := by
    unfold signed
    decide +kernel
  exact hh side k other i

private theorem adjacentGenerator_image (side : Bool) (k : Fin 3) :
    toProduct (adjacentGenerator side k) =
      if side then (1,Equiv.swap k.castSucc k.succ) else (Equiv.swap k.castSucc k.succ,1) := by
  cases side
  · apply Prod.ext <;> apply Equiv.ext <;> intro i
    · exact imageIndex_eq _ _ _ _ (generator_action false k false i)
    · exact imageIndex_eq _ _ _ _ (generator_action false k true i)
  · apply Prod.ext <;> apply Equiv.ext <;> intro i
    · exact imageIndex_eq _ _ _ _ (generator_action true k false i)
    · exact imageIndex_eq _ _ _ _ (generator_action true k true i)

/-- Every pair of four-point permutations is induced by a literal triangle
stabilizer element. The witnesses are products of explicit commutators. -/
theorem toProduct_surjective : Function.Surjective toProduct := by
  let K := toProduct.range
  have hfirst (p : Equiv.Perm (Fin 4)) : (p,1) ∈ K := by
    let J := K.comap (MonoidHom.inl (Equiv.Perm (Fin 4)) (Equiv.Perm (Fin 4)))
    have ht : J = ⊤ := by
      apply Subgroup.toSubmonoid_injective
      apply top_unique
      rw [←Equiv.Perm.mclosure_swap_castSucc_succ 3]
      apply Submonoid.closure_le.mpr
      rintro _ ⟨k,rfl⟩
      exact ⟨adjacentGenerator false k,adjacentGenerator_image false k⟩
    change p ∈ J
    rw [ht]
    exact Subgroup.mem_top p
  have hsecond (p : Equiv.Perm (Fin 4)) : (1,p) ∈ K := by
    let J := K.comap (MonoidHom.inr (Equiv.Perm (Fin 4)) (Equiv.Perm (Fin 4)))
    have ht : J = ⊤ := by
      apply Subgroup.toSubmonoid_injective
      apply top_unique
      rw [←Equiv.Perm.mclosure_swap_castSucc_succ 3]
      apply Submonoid.closure_le.mpr
      rintro _ ⟨k,rfl⟩
      exact ⟨adjacentGenerator true k,adjacentGenerator_image true k⟩
    change p ∈ J
    rw [ht]
    exact Subgroup.mem_top p
  rintro ⟨p,q⟩
  change (p,q) ∈ K
  simpa only [Prod.mul_def,mul_one,one_mul] using K.mul_mem (hfirst p) (hsecond q)

/-- The triangle-span factor comes first; the complement factor comes second. -/
noncomputable def productEquiv : H ≃* Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) :=
  MulEquiv.ofBijective toProduct ⟨toProduct_injective,toProduct_surjective⟩

end OmegaSixThree.TriangleLocal
