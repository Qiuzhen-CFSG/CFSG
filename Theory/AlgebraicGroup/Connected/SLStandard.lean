module

public import Theory.AlgebraicGroup.Instance.SL
public import Theory.AlgebraicGroup.Variety.AffineSpace

/-!
The determinant-one standard special-linear variety is connected in every
positive matrix size.  The one-dimensional case is a singleton.  In higher
rank, every special-linear matrix is reduced to diagonal and transvection
generators; transvections lie in the identity component as polynomial images
of connected affine one-space, while each two-entry diagonal generator is a
product of six transvections.
-/

set_option warningAsError false

universe u

namespace Theory.AlgebraicGroup

public theorem sl_standard_variety_isConnected
    {k : Type u} [Field k] [IsAlgClosed k] (m : ℕ) :
    Variety.IsConnected (slVarietyOf k (Fin (m + 1) → k)) := by
  classical
  cases m with
  | zero =>
      have huniv :
          (Set.univ : Set (Variety.Point (slVariety k 1))) = {1} := by
        ext x
        simp only [Set.mem_univ, Set.mem_singleton_iff, true_iff]
        apply (slPointEquiv 1).injective
        change slPointEquiv 1 x =
          (1 : Matrix.SpecialLinearGroup (Fin 1) k)
        apply Subtype.ext
        ext i j
        fin_cases i
        fin_cases j
        simpa using (slPointEquiv 1 x).2
      have hconnected : Variety.IsConnected (slVariety k 1) := by
        change _root_.IsConnected
          (Set.univ : Set (Variety.Point (slVariety k 1)))
        rw [huniv]
        exact isConnected_singleton
      simpa [slVarietyOf, Module.finrank_pi_fintype] using hconnected
  | succ m =>
      let n := m + 2
      let H := AlgebraicGroup.identityComponentSubgroup (slVariety k n)
      have hmul : ∀ A B : Matrix.SpecialLinearGroup (Fin n) k,
          (slPointEquiv n).symm A ∈ H →
          (slPointEquiv n).symm B ∈ H →
          (slPointEquiv n).symm (A * B) ∈ H := by
        intro A B hA hB
        change (slPointEquiv n).symm A * (slPointEquiv n).symm B ∈ H
        exact H.mul_mem hA hB
      have htransvec : ∀ (i j : Fin n) (hij : i ≠ j) (a : k),
          (slPointEquiv n).symm
              (Matrix.SpecialLinearGroup.transvection hij a) ∈ H := by
        intro i j hij a
        let f : Variety.Morphism (affineSpaceVariety k PUnit)
            (slVariety k n) :=
          { toFun := fun t ↦
              (slPointEquiv n).symm
                (Matrix.SpecialLinearGroup.transvection hij
                  (t.val PUnit.unit))
            regular := by
              intro q
              rcases q with ⟨⟨r, s⟩⟩
              refine ⟨MvPolynomial.C
                    ((1 : Matrix (Fin n) (Fin n) k) r s) +
                  MvPolynomial.C
                      ((Matrix.single i j (1 : k)) r s) *
                    MvPolynomial.X PUnit.unit, ?_⟩
              intro t
              change
                ((Matrix.SpecialLinearGroup.transvection hij
                    (t.val PUnit.unit) :
                      Matrix.SpecialLinearGroup (Fin n) k) :
                    Matrix (Fin n) (Fin n) k) r s = _
              rw [Matrix.SpecialLinearGroup.transvection_coe]
              by_cases hrs : i = r ∧ j = s
              · simp [evalPolynomial, hrs]
              · simp [evalPolynomial, hrs] }
        have hrange : _root_.IsConnected (Set.range f.toFun) := by
          simpa only [Set.image_univ] using
            (affineSpaceVariety_isConnected (k := k) (σ := PUnit)).image
              f.toFun f.continuous.continuousOn
        have hone :
            (1 : Variety.Point (slVariety k n)) ∈ Set.range f.toFun := by
          refine ⟨affineSpacePoint (fun _ : PUnit ↦ (0 : k)), ?_⟩
          apply (slPointEquiv n).injective
          dsimp [f]
          rw [(slPointEquiv n).apply_symm_apply]
          change Matrix.SpecialLinearGroup.transvection hij 0 =
            (1 : Matrix.SpecialLinearGroup (Fin n) k)
          exact Matrix.SpecialLinearGroup.transvection_coeff_zero hij
        have haRange : f.toFun
            (affineSpacePoint (fun _ : PUnit ↦ a)) ∈ Set.range f.toFun :=
          Set.mem_range_self _
        have haComponent :=
          hrange.subset_connectedComponent hone haRange
        change (slPointEquiv n).symm
            (Matrix.SpecialLinearGroup.transvection hij a) ∈
          connectedComponent (1 : Variety.Point (slVariety k n)) at haComponent
        exact haComponent
      have hdiag : ∀ (i j : Fin n) (hij : i ≠ j) {c : k},
          ∀ hc : c ≠ 0,
          (slPointEquiv n).symm
              (Matrix.SpecialLinearGroup.diag2n hij c hc) ∈ H := by
        intro i j hij c hc
        have hdecomp :
            Matrix.SpecialLinearGroup.diag2n hij c hc =
              Matrix.SpecialLinearGroup.transvection hij c *
                Matrix.SpecialLinearGroup.transvection hij.symm (-c⁻¹) *
                Matrix.SpecialLinearGroup.transvection hij c *
                Matrix.SpecialLinearGroup.transvection hij (-1) *
                Matrix.SpecialLinearGroup.transvection hij.symm 1 *
                Matrix.SpecialLinearGroup.transvection hij (-1) := by
          apply Subtype.ext
          ext r s
          simp [Matrix.SpecialLinearGroup.diag2n_coe,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.diagonal_apply, mul_add, add_mul,
            Matrix.single_mul_single_of_ne _ _ _ _ hij,
            Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
            mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]
          by_cases hri : r = i <;> by_cases hrj : r = j <;>
            by_cases hsi : s = i <;> by_cases hsj : s = j <;>
            by_cases hrs : r = s <;>
            simp_all [Matrix.one_apply, Matrix.single_apply, eq_comm]
        rw [hdecomp]
        exact hmul _ _
          (hmul _ _
            (hmul _ _
              (hmul _ _
                (hmul _ _ (htransvec i j hij c)
                  (htransvec j i hij.symm (-c⁻¹)))
                (htransvec i j hij c))
              (htransvec i j hij (-1)))
            (htransvec j i hij.symm 1))
          (htransvec i j hij (-1))
      have hconnected : Variety.IsConnected (slVariety k n) := by
        apply (identityComponent_eq_univ_iff_isConnected
          (slVariety k n)).mp
        apply Set.eq_univ_of_univ_subset
        intro x _hx
        change x ∈ H
        have hx :=
          Matrix.SpecialLinearGroup.diagonal_transvection_induction'
            (fun A ↦ (slPointEquiv n).symm A ∈ H)
            (slPointEquiv n x) hdiag htransvec hmul
        simpa using hx
      simpa [slVarietyOf, Module.finrank_pi_fintype, n,
        Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hconnected

end Theory.AlgebraicGroup
