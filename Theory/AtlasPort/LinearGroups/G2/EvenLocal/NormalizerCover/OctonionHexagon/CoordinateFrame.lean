module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The basis-product argument is adapted from Atlas/LinearGroups/G2/SingularAction.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: identify the six-coordinate-line stabilizer with the split torus and
transport it to the actual parabolic coset action.
-/

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.CosetGeometry

/-!
# The six coordinate points and their pointwise stabilizer

An automorphism fixing the six off-diagonal singular lines scales their basis
vectors. Norm preservation pairs the scalars as inverses, while the product of
basis vectors 1 and 2 forces the remaining relation. Products of opposite basis
vectors determine the two diagonal vectors. The resulting automorphism is
exactly the existing two-parameter split torus.

The equivariant long-coset identification transports this computation to actual
vertices. Over a finite field of characteristic two the torus has odd order;
therefore so does the pointwise stabilizer of any vertex set containing a
translate of the six coordinate points. Placing these points on an arbitrary
twelve-cycle is a separate geometric assertion, not assumed by the computation.

Source context: the defining-characteristic rank-two argument for
Aschbacher--Smith, Theorem 0.1.2(1), printed pp.3--4, repeated as Theorem 0.1.1
on pp.481--482. Octonion coordinates use the licensed ATLAS port.
-/

@[expose] public section

open Atlas.G2 Atlas.SplitOctonion
open scoped LinearAlgebra.Projectivization

namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
variable {F : Type*} [Field F]

private theorem vector_ne_zero (i : Fin 8) : (basisVector i : Carrier F) ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [basisVector] at hi

theorem offDiagonalVector_ne_zero (i : Fin 6) :
    offDiagonalVector (F := F) i ≠ 0 := vector_ne_zero _

noncomputable def coordinatePoint (i : Fin 6) : SingularPoints F :=
  singularPointMk F (offDiagonalVector i) (offDiagonalVector_ne_zero i)
    (offDiagonal_singular i).1 (offDiagonal_singular i).2

theorem coordinatePoint_fixed_iff (g : Model F) (i : Fin 6) :
    g • coordinatePoint (F := F) i = coordinatePoint i ↔
      ∃ a : Fˣ, g.val (offDiagonalVector i) = (a : F) • offDiagonalVector i := by
  rw [coordinatePoint, singularPointMk_smul]
  constructor
  · intro h
    have h := congrArg Subtype.val h
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp h
    exact ⟨a, by simpa only [Units.smul_def] using ha.symm⟩
  · rintro ⟨a,ha⟩
    apply Subtype.ext
    apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
    exact ⟨a, by simpa only [Units.smul_def] using ha.symm⟩


private theorem diagonal_eq_torus (g : Model F) (c : Fin 6 → Fˣ)
    (hc : ∀ i, g.val (offDiagonalVector i) = (c i : F) • offDiagonalVector i) :
    g = torus (c 0) (c 1) := by
  have h05 : (c 0 : F) * (c 5 : F) = 1 := by
    have h := automorphism_norm g (offDiagonalVector 0 + offDiagonalVector 5)
    rw [map_add, hc, hc] at h
    simpa [offDiagonalVector, offDiagonalIndex, basisVector, SplitOctonion.norm] using h
  have h14 : (c 1 : F) * (c 4 : F) = 1 := by
    have h := automorphism_norm g (offDiagonalVector 1 + offDiagonalVector 4)
    rw [map_add, hc, hc] at h
    simpa [offDiagonalVector, offDiagonalIndex, basisVector, SplitOctonion.norm] using h
  have h23 : (c 2 : F) * (c 3 : F) = 1 := by
    have h := automorphism_norm g (offDiagonalVector 2 + offDiagonalVector 3)
    rw [map_add, hc, hc] at h
    simpa [offDiagonalVector, offDiagonalIndex, basisVector, SplitOctonion.norm] using h
  have hp12 : mul (offDiagonalVector (F := F) 1) (offDiagonalVector 2) =
      -offDiagonalVector 0 := by
    funext i
    fin_cases i <;> simp [mul, offDiagonalVector, offDiagonalIndex, basisVector]
  have h12 : (c 1 : F) * (c 2 : F) = c 0 := by
    have h := automorphism_mul g (offDiagonalVector 1) (offDiagonalVector 2)
    rw [hp12, map_neg, hc, hc, hc, SplitOctonion.smul_mul,
      SplitOctonion.mul_smul, hp12] at h
    have h0 := congrFun h 0
    simpa [offDiagonalVector, offDiagonalIndex, basisVector] using h0.symm
  have he2 : (c 2 : F) = (c 0 : F) * (c 1 : F)⁻¹ := by
    apply mul_left_cancel₀ (c 1).ne_zero
    rw [h12]
    field_simp
  have he3 : (c 3 : F) = (c 0 : F)⁻¹ * (c 1 : F) := by
    apply mul_left_cancel₀ (c 2).ne_zero
    rw [h23, he2]
    field_simp
  have he4 : (c 4 : F) = (c 1 : F)⁻¹ := by
    apply mul_left_cancel₀ (c 1).ne_zero
    rw [h14, mul_inv_cancel₀ (c 1).ne_zero]
  have he5 : (c 5 : F) = (c 0 : F)⁻¹ := by
    apply mul_left_cancel₀ (c 0).ne_zero
    rw [h05, mul_inv_cancel₀ (c 0).ne_zero]
  have hp3 : mul (offDiagonalVector (F := F) 0) (offDiagonalVector 5) =
      -(basisVector 3 : Carrier F) := by
    funext i
    fin_cases i <;> simp [mul, offDiagonalVector, offDiagonalIndex, basisVector]
  have hp4 : mul (offDiagonalVector (F := F) 5) (offDiagonalVector 0) =
      -(basisVector 4 : Carrier F) := by
    funext i
    fin_cases i <;> simp [mul, offDiagonalVector, offDiagonalIndex, basisVector]
  have hf3 : g.val (basisVector 3) = basisVector 3 := by
    have h := automorphism_mul g (offDiagonalVector 0) (offDiagonalVector 5)
    rw [hp3, map_neg, hc, hc, SplitOctonion.smul_mul,
      SplitOctonion.mul_smul, hp3, smul_smul, h05, one_smul] at h
    exact neg_injective h
  have hf4 : g.val (basisVector 4) = basisVector 4 := by
    have h := automorphism_mul g (offDiagonalVector 5) (offDiagonalVector 0)
    rw [hp4, map_neg, hc, hc, SplitOctonion.smul_mul,
      SplitOctonion.mul_smul, hp4, smul_smul, mul_comm (c 5 : F), h05, one_smul] at h
    exact neg_injective h
  have hb (i : Fin 8) : g.val (basisVector i) =
      (torus (c 0) (c 1)).val (basisVector i) := by
    have ht (j : Fin 6) : g.val (offDiagonalVector j) =
        (torus (c 0) (c 1)).val (offDiagonalVector j) := by
      rw [hc]
      fin_cases j <;> ext k <;> fin_cases k <;>
        simp [torus, torusEquiv, torusLinear, torusWeights, basisVector,
          offDiagonalVector, offDiagonalIndex, he2, he3, he4, he5]
    fin_cases i
    · exact ht 0
    · exact ht 1
    · exact ht 2
    · change g.val (basisVector 3) = _
      rw [hf3]; ext k; fin_cases k <;>
        simp [torus, torusEquiv, torusLinear, torusWeights, basisVector]
    · change g.val (basisVector 4) = _
      rw [hf4]; ext k; fin_cases k <;>
        simp [torus, torusEquiv, torusLinear, torusWeights, basisVector]
    · exact ht 3
    · exact ht 4
    · exact ht 5
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact (Pi.basisFun F (Fin 8)).ext (fun i => by
    simpa [Pi.basisFun_apply, basisVector] using hb i)



/-- Fixing the six singular coordinate lines is exactly membership in the split torus. -/
theorem fixes_coordinatePoints_iff (g : Model F) :
    (∀ i : Fin 6, g • coordinatePoint (F := F) i = coordinatePoint i) ↔
      g ∈ splitTorus := by
  constructor
  · intro hg
    choose c hc using fun i => (coordinatePoint_fixed_iff g i).mp (hg i)
    exact ⟨(c 0, c 1), (diagonal_eq_torus g c hc).symm⟩
  · rintro ⟨⟨a,b⟩,rfl⟩ i
    apply (coordinatePoint_fixed_iff _ i).mpr
    refine ⟨torusWeights a b (offDiagonalIndex i), ?_⟩
    fin_cases i <;> ext j <;> fin_cases j <;>
      simp [torusHom, torus, torusEquiv, torusLinear, torusWeights,
        offDiagonalVector, offDiagonalIndex, basisVector]

/-- The corresponding vertex of the actual long parabolic coset space. -/
noncomputable def coordinateLongVertex (i : Fin 6) : Vertex F :=
  Sum.inr (longCosetEquivSingularPoints.symm (coordinatePoint i))

theorem coordinateLongVertex_fixed_iff (g : Model F) (i : Fin 6) :
    g • coordinateLongVertex (F := F) i = coordinateLongVertex i ↔
      g • coordinatePoint (F := F) i = coordinatePoint i := by
  change Sum.inr (g • longCosetEquivSingularPoints.symm (coordinatePoint i)) =
    (Sum.inr (longCosetEquivSingularPoints.symm (coordinatePoint i)) : Vertex F) ↔ _
  rw [Sum.inr.injEq, ← longCosetEquivSingularPoints.injective.eq_iff,
    longCosetEquivSingularPoints_smul, Equiv.apply_symm_apply]

/-- The pointwise stabilizer of these six actual long vertices is the existing split torus. -/
theorem fixing_coordinateLongVertices :
    fixingSubgroup (Model F) (Set.range (coordinateLongVertex (F := F))) = splitTorus := by
  ext g
  rw [mem_fixingSubgroup_iff]
  simp only [Set.forall_mem_range, coordinateLongVertex_fixed_iff]
  exact fixes_coordinatePoints_iff g

/-- The split torus has odd order over every finite field of characteristic two. -/
theorem splitTorus_odd [Finite F] [CharP F 2] :
    Odd (Nat.card (splitTorus (K := F))) := by
  rw [card_splitTorus]
  obtain ⟨n,hn,hcard⟩ := LieParabolicSetup.field_card (F := F)
  have heven : Even (Nat.card F) := by
    rw [hcard]
    exact even_two.pow_of_ne_zero (Nat.ne_of_gt hn)
  exact (Nat.Even.sub_odd (Nat.succ_le_of_lt Nat.card_pos) heven odd_one).pow

/-- Any configuration containing a translate of the six coordinate points
has odd pointwise stabilizer. -/
theorem fixing_odd_of_contains_coordinateLongVertices [Finite F] [CharP F 2]
    (s : Set (Vertex F)) (g : Model F)
    (hs : ∀ i : Fin 6, g • coordinateLongVertex (F := F) i ∈ s) :
    Odd (Nat.card (fixingSubgroup (Model F) s)) := by
  have hle : (fixingSubgroup (Model F) s).map (MulAut.conj g⁻¹).toMonoidHom ≤
      fixingSubgroup (Model F) (Set.range (coordinateLongVertex (F := F))) := by
    rintro k ⟨h,hh,rfl⟩
    rw [mem_fixingSubgroup_iff]
    rintro _ ⟨i,rfl⟩
    have hfix := (mem_fixingSubgroup_iff (Model F)).mp hh _ (hs i)
    change (g⁻¹ * h * (g⁻¹)⁻¹) • coordinateLongVertex i = coordinateLongVertex i
    rw [inv_inv, SemigroupAction.mul_smul, SemigroupAction.mul_smul, hfix, inv_smul_smul]
  rw [fixing_coordinateLongVertices] at hle
  have hodd := (splitTorus_odd (F := F)).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at hodd

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
