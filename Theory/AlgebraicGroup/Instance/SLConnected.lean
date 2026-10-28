module

public import Theory.AlgebraicGroup.Instance.SL
public import Theory.AlgebraicGroup.Tori.Power
public import Theory.AlgebraicGroup.Variety.AffineSpace

/-!
The determinant-one matrix variety is connected.  In dimensions zero and one
its point space is a singleton.  In higher dimensions, the proof uses the
canonical equivalence with the matrix special linear group: polynomial families
over the affine line and the one-dimensional diagonal group put elementary
transvections and two-entry determinant-one diagonal matrices in the identity
component.  The diagonal/transvection decomposition of a special linear matrix
then shows that every point belongs to that component.
-/

set_option warningAsError false

namespace Theory.AlgebraicGroup

public theorem slVariety_isConnected
    {k : Type*} [Field k] [IsAlgClosed k] (n : ℕ) :
    Variety.IsConnected (slVariety k n) := by
  apply (identityComponent_eq_univ_iff_isConnected (slVariety k n)).mp
  apply Set.eq_univ_of_univ_subset
  intro x _hx
  cases n with
  | zero =>
      have hx : x = 1 := by
        apply (slPointEquiv (k := k) 0).injective
        exact Subsingleton.elim _ _
      subst x
      exact one_mem_identityComponent (slVariety k 0)
  | succ n =>
      cases n with
      | zero =>
          have hx : x = 1 := by
            apply (slPointEquiv (k := k) 1).injective
            exact Subsingleton.elim _ _
          subst x
          exact one_mem_identityComponent (slVariety k 1)
      | succ m =>
          let P : Matrix.SpecialLinearGroup (Fin (m + 2)) k → Prop :=
            fun A => (slPointEquiv (k := k) (m + 2)).symm A ∈
              AlgebraicGroup.identityComponent (slVariety k (m + 2))
          have htransvection (i j : Fin (m + 2)) (hij : i ≠ j) (a : k) :
              P (Matrix.SpecialLinearGroup.transvection hij a) := by
            let f : Variety.Morphism (affineSpaceVariety k PUnit) (slVariety k (m + 2)) :=
              { toFun := fun z => (slPointEquiv (k := k) (m + 2)).symm
                  (Matrix.SpecialLinearGroup.transvection hij (z.val PUnit.unit))
                regular := by
                  rintro ⟨⟨r, s⟩⟩
                  refine ⟨MvPolynomial.C ((1 : Matrix (Fin (m + 2)) (Fin (m + 2)) k) r s) +
                      if i = r ∧ j = s then MvPolynomial.X PUnit.unit else 0, ?_⟩
                  intro z
                  change ((Matrix.SpecialLinearGroup.transvection hij (z.val PUnit.unit) :
                      Matrix.SpecialLinearGroup (Fin (m + 2)) k) :
                        Matrix (Fin (m + 2)) (Fin (m + 2)) k) r s = _
                  rw [Matrix.SpecialLinearGroup.transvection_coe]
                  by_cases h : i = r ∧ j = s <;>
                    simp [h, evalPolynomial] }
            let z : k → Variety.Point (affineSpaceVariety k PUnit) := fun b =>
              affineSpacePoint (fun _ => b)
            have hsource : Variety.IsConnected (affineSpaceVariety k PUnit) := by
              exact affineSpaceVariety_isConnected
            have hrange : _root_.IsConnected (Set.range f.toFun) := by
              simpa only [Set.image_univ] using
                hsource.image f.toFun f.continuous.continuousOn
            have hzero : f.toFun (z 0) = 1 := by
              change (slPointEquiv (k := k) (m + 2)).symm
                  (Matrix.SpecialLinearGroup.transvection hij 0) =
                (slPointEquiv (k := k) (m + 2)).symm 1
              rw [Matrix.SpecialLinearGroup.transvection_coeff_zero]
            have ha : f.toFun (z a) =
                (slPointEquiv (k := k) (m + 2)).symm
                  (Matrix.SpecialLinearGroup.transvection hij a) := by
              rfl
            exact (hrange.subset_connectedComponent ⟨z 0, hzero⟩) ⟨z a, ha⟩
          have hdiagonal (i j : Fin (m + 2)) (hij : i ≠ j)
              {c : k} (hc : c ≠ 0) :
              P (Matrix.SpecialLinearGroup.diag2n hij c hc) := by
            let f : Variety.Morphism (dVariety k 1) (slVariety k (m + 2)) :=
              { toFun := fun z => (slPointEquiv (k := k) (m + 2)).symm
                  (Matrix.SpecialLinearGroup.diag2n hij (dPointEntry 1 z 0)
                    (dPoint_entry_isUnit 1 z 0).ne_zero)
                regular := by
                  rintro ⟨⟨r, s⟩⟩
                  refine ⟨if r = s then
                      if r = i then MvPolynomial.X (Sum.inl (ULift.up (0 : Fin 1)))
                      else if r = j then MvPolynomial.X (Sum.inr (ULift.up (0 : Fin 1)))
                      else MvPolynomial.C 1
                    else MvPolynomial.C 0, ?_⟩
                  intro z
                  change (Matrix.SpecialLinearGroup.diag2n hij (dPointEntry 1 z 0)
                      (dPoint_entry_isUnit 1 z 0).ne_zero).1 r s = _
                  rw [Matrix.SpecialLinearGroup.diag2n_coe]
                  by_cases hrs : r = s
                  · subst s
                    by_cases hri : r = i
                    · simp [hri, evalPolynomial, dPointEntry]
                    · by_cases hrj : r = j
                      · have hji : j ≠ i := by
                          intro h
                          exact hri (hrj.trans h)
                        simp [hrj, hji, evalPolynomial, dPointEntryInv,
                          dPoint_entry_inv]
                      · simp [hri, hrj, evalPolynomial]
                  · simp [hrs, evalPolynomial] }
            have hsource : Variety.IsConnected (dVariety k 1) :=
              dVariety_isConnected 1
            have hrange : _root_.IsConnected (Set.range f.toFun) := by
              simpa only [Set.image_univ] using
                hsource.image f.toFun f.continuous.continuousOn
            have honeEntry : dPointEntry 1 (1 : Variety.Point (dVariety k 1)) 0 = 1 := by
              change (((dPointEquiv 1 (1 : Variety.Point (dVariety k 1))) 0 : kˣ) : k) = 1
              rw [dPointEquiv_one]
              rfl
            have hone : f.toFun (1 : Variety.Point (dVariety k 1)) = 1 := by
              change (slPointEquiv (k := k) (m + 2)).symm
                  (Matrix.SpecialLinearGroup.diag2n hij
                    (dPointEntry 1 (1 : Variety.Point (dVariety k 1)) 0) _) =
                (slPointEquiv (k := k) (m + 2)).symm 1
              apply (slPointEquiv (k := k) (m + 2)).injective
              simp only [Equiv.apply_symm_apply]
              ext r s
              simp [Matrix.SpecialLinearGroup.diag2n_coe, honeEntry,
                Matrix.diagonal_apply, Matrix.one_apply]
            let zc : Variety.Point (dVariety k 1) :=
              (dPointEquiv 1).symm (fun _ => Units.mk0 c hc)
            have hzcEntry : dPointEntry 1 zc 0 = c := by
              rfl
            have hzc : f.toFun zc = (slPointEquiv (k := k) (m + 2)).symm
                (Matrix.SpecialLinearGroup.diag2n hij c hc) := by
              change (slPointEquiv (k := k) (m + 2)).symm
                  (Matrix.SpecialLinearGroup.diag2n hij (dPointEntry 1 zc 0) _) = _
              apply (slPointEquiv (k := k) (m + 2)).injective
              simp only [Equiv.apply_symm_apply]
              ext r s
              simp [Matrix.SpecialLinearGroup.diag2n_coe, hzcEntry]
            exact (hrange.subset_connectedComponent ⟨1, hone⟩) ⟨zc, hzc⟩
          have hmul (A B : Matrix.SpecialLinearGroup (Fin (m + 2)) k)
              (hA : P A) (hB : P B) : P (A * B) := by
            exact (AlgebraicGroup.identityComponentSubgroup (slVariety k (m + 2))).mul_mem hA hB
          have hall := Matrix.SpecialLinearGroup.diagonal_transvection_induction'
            P (slPointEquiv (k := k) (m + 2) x) hdiagonal htransvection hmul
          simpa [P] using hall

end Theory.AlgebraicGroup
