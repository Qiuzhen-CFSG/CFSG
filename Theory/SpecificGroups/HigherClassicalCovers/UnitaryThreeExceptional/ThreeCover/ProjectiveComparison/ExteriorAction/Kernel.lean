module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.ProjectiveComparison.UnitaryGeometry
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorKernel

/-!
# Exhausting the kernel on the 252 nonisotropic sign classes

A linear map fixing these sign classes acts as a common sign on all six real
basis vectors: each basis vector and each sum with the first basis vector has
nonzero norm. Those six vectors also span the exterior space over F₉, so the
entire exterior action is plus or minus the identity. Scaling by a square root
of minus one reduces the second case to the existing exterior-kernel theorem.
Thus a four-dimensional matrix whose exterior action fixes all points is scalar.

This uses the literal published point catalogue and compound matrices. The
imported exterior-kernel proof is the attributed ATLAS port (copyright Gerald
Höhn and ATLAS contributors; see LICENSES/ATLAS.txt). Source: the classical
exterior-square construction, GLS3 §2.7, used in the I.1.4(5) cover comparison.

-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.UnitaryGeometry
open Matrix Atlas.Order20160A8.Bivectors
open Theory.SpecificGroups.ClassicalUnitary


local notation "E" => FiniteField.Nine

theorem bivector_add (v w : Vector) : bivector (v + w) = bivector v + bivector w := by
  have hp (i j : Fin 6) : pair (v + w) i j = pair v i j + pair w i j := rfl
  funext i
  fin_cases i <;> simp [bivector, hp, add_comm]

private def realBasis (i : Fin 6) : Six E := bivector (Pi.single i 1)

private theorem realBasis_ne_neg (i : Fin 6) : realBasis i ≠ -realBasis i := by
  intro h
  have he := bivector_injective (h.trans (bivector_neg _).symm)
  have hi : (1 : ZMod 3) = -1 := by simpa using congrFun he i
  exact (by decide : (1 : ZMod 3) ≠ -1) hi

private theorem basis_norm : ∀ i : Fin 6, norm (Pi.single i 1) ≠ 0 := by decide
private theorem basis_add_norm : ∀ i : Fin 6,
    norm (Pi.single 0 1 + Pi.single i 1) ≠ 0 := by decide

private theorem fixes_nonisotropic (L : Six E →ₗ[E] Six E)
    (h : ∀ i, L (point i) = point i ∨ L (point i) = -point i)
    (v : Vector) (hv : norm v ≠ 0) :
    L (bivector v) = bivector v ∨ L (bivector v) = -bivector v := by
  rcases coordinates_complete v hv with he | he
  · rw [he]
    exact h (indexOf v)
  · rw [he, bivector_neg, map_neg]
    rcases h (indexOf v) with hh | hh
    · exact Or.inl (congrArg Neg.neg hh)
    · exact Or.inr (congrArg Neg.neg hh)

private theorem common_basis_sign (L : Six E →ₗ[E] Six E)
    (h : ∀ i, L (point i) = point i ∨ L (point i) = -point i) :
    (∀ i, L (realBasis i) = realBasis i) ∨
      (∀ i, L (realBasis i) = -realBasis i) := by
  have hb (i : Fin 6) := fixes_nonisotropic L h (Pi.single i 1) (basis_norm i)
  change ∀ i, L (realBasis i) = realBasis i ∨ L (realBasis i) = -realBasis i at hb
  have hs (i : Fin 6) := fixes_nonisotropic L h
    (Pi.single 0 1 + Pi.single i 1) (basis_add_norm i)
  simp only [bivector_add, map_add] at hs
  change ∀ i, L (realBasis 0) + L (realBasis i) = realBasis 0 + realBasis i ∨
    L (realBasis 0) + L (realBasis i) = -(realBasis 0 + realBasis i) at hs
  rcases hb 0 with h0 | h0
  · left
    intro i
    rcases hb i with hi | hi
    · exact hi
    · have hh := hs i
      rw [h0, hi] at hh
      rcases hh with hh | hh
      · exact (realBasis_ne_neg i (add_left_cancel hh).symm).elim
      · rw [neg_add] at hh
        exact (realBasis_ne_neg 0 (add_right_cancel hh)).elim
  · right
    intro i
    rcases hb i with hi | hi
    · have hh := hs i
      rw [h0, hi] at hh
      rcases hh with hh | hh
      · exact (realBasis_ne_neg 0 (add_right_cancel hh).symm).elim
      · rw [neg_add] at hh
        exact (realBasis_ne_neg i (add_left_cancel hh)).elim
    · exact hi

-- The six real basis vectors also span after extending scalars to F₉.
private def imaginary : E := ⟨0, 1⟩
private def reconstruction (w : Six E) : Fin 6 → E :=
  ![-(w 0 + w 5), imaginary * (w 0 - w 5),
    -(w 1 - w 4), imaginary * (w 1 + w 4),
    -(w 2 + w 3), imaginary * (w 2 - w 3)]

private theorem reconstruct (w : Six E) :
    ∑ i, reconstruction w i • realBasis i = w := by
  have htwo : (2 : ZMod 3) = -1 := by decide
  funext j
  fin_cases j <;> apply QuadraticAlgebra.ext <;>
    simp [reconstruction, realBasis, bivector, pair, imaginary, Fin.sum_univ_succ,
      smul_eq_mul] <;> ring_nf <;> simp only [htwo, mul_neg, mul_one, neg_neg]

theorem scalar_sign_of_fixes_points (L : Six E →ₗ[E] Six E)
    (h : ∀ i, L (point i) = point i ∨ L (point i) = -point i) :
    (∀ w, L w = w) ∨ (∀ w, L w = -w) := by
  rcases common_basis_sign L h with hh | hh
  · left
    intro w
    calc L w = L (∑ i, reconstruction w i • realBasis i) := congrArg L (reconstruct w).symm
         _ = ∑ i, reconstruction w i • realBasis i := by simp only [map_sum, map_smul, hh]
         _ = w := reconstruct w
  · right
    intro w
    calc L w = L (∑ i, reconstruction w i • realBasis i) := congrArg L (reconstruct w).symm
         _ = -(∑ i, reconstruction w i • realBasis i) := by
           simp only [map_sum, map_smul, hh, smul_neg, Finset.sum_neg_distrib]
         _ = -w := congrArg Neg.neg (reconstruct w)



theorem exteriorMap_smul (c : E) (A : Matrix (Fin 4) (Fin 4) E) (w : Six E) :
    exteriorMap (c • A) w = c ^ 2 • exteriorMap A w := by
  have hc : compound (c • A) = c ^ 2 • compound A := by
    funext i j
    simp only [compound, Matrix.smul_apply, smul_eq_mul]
    ring
  change compound (c • A) *ᵥ w = c ^ 2 • (compound A *ᵥ w)
  rw [hc, Matrix.smul_mulVec]

theorem scalar_of_exterior_sign (A : Matrix (Fin 4) (Fin 4) E)
    (h : (∀ w, exteriorMap A w = w) ∨ (∀ w, exteriorMap A w = -w)) :
    ∃ c : E, A = c • 1 := by
  rcases h with h | h
  · obtain ⟨c, _, hc⟩ := scalar_of_exteriorMap_eq_id A h
    exact ⟨c, hc⟩
  · let t : E := ⟨0, 1⟩
    have ht : t ^ 2 = -1 := by decide
    have he : ∀ w, exteriorMap (t • A) w = w := by
      intro w
      rw [exteriorMap_smul, h, ht, neg_one_smul, neg_neg]
    obtain ⟨c, _, hc⟩ := scalar_of_exteriorMap_eq_id (t • A) he
    refine ⟨-t * c, ?_⟩
    have htt : -t * t = 1 := by rw [neg_mul, ← pow_two, ht, neg_neg]
    have hh := congrArg (fun B : Matrix (Fin 4) (Fin 4) E => (-t) • B) hc
    simpa only [smul_smul, htt, one_smul] using hh


end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.UnitaryGeometry
