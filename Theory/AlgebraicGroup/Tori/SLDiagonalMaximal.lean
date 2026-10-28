module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_6

/-!
This module constructs the standard diagonal maximal torus in
`SL_(m+1)`.  It is the closed image of `D_m`, embedded by using the first
`m` torus coordinates as diagonal entries and their inverse product as the
last entry.  The determinant equation proves that this image is exactly the
determinant-one diagonal subgroup, including in rank zero.

For maximality, a torus containing this subgroup is commutative.  Given two
distinct matrix indices, a determinant-one diagonal element with entries
`a` and `a⁻¹`, where `a² ≠ 1`, forces the corresponding off-diagonal entry of
every element of the larger torus to vanish.  Thus the larger torus already
lies in the constructed diagonal subgroup.  This is the standard geometric
construction of the diagonal maximal torus of the special linear group.
-/

set_option warningAsError false

namespace Theory.AlgebraicGroup

public theorem slVariety_exists_diagonal_maximalTorus
    {k : Type*} [Field k] [IsAlgClosed k] (m : ℕ) :
    ∃ T : ClosedSubgroup (slVariety k (m + 1)),
      IsMaximalTorus T ∧
      ∀ g : Variety.Point (slVariety k (m + 1)),
        g ∈ T ↔ ∀ i j : Fin (m + 1), i ≠ j →
          slPointMatrix (m + 1) g i j = 0 := by
  classical
  let diagonalEntry (x : Variety.Point (dVariety k m)) : Fin (m + 1) → k :=
    Fin.snoc (fun i => dPointEntry m x i) (∏ i, dPointEntryInv m x i)
  let diagonalPoint (x : Variety.Point (dVariety k m)) :
      Variety.Point (slVariety k (m + 1)) :=
    (slPointEquiv (m + 1)).symm
      ⟨Matrix.diagonal (diagonalEntry x), by
        rw [Matrix.det_diagonal, Fin.prod_univ_castSucc]
        simp only [diagonalEntry, Fin.snoc_castSucc, Fin.snoc_last]
        rw [← Finset.prod_mul_distrib]
        simp [dPoint_entry_mul_inv]⟩
  have diagonalPoint_matrix (x : Variety.Point (dVariety k m)) :
      slPointMatrix (m + 1) (diagonalPoint x) =
        Matrix.diagonal (diagonalEntry x) := by
    change ((slPointEquiv (m + 1)) (diagonalPoint x)).1 = _
    exact congrArg Subtype.val ((slPointEquiv (m + 1)).apply_symm_apply _)
  let diagonalMorphism :
      AlgebraicGroup.Morphism (dVariety k m) (slVariety k (m + 1)) :=
    { toVariety :=
        { toFun := diagonalPoint
          regular := by
            rintro ⟨⟨i, j⟩⟩
            by_cases hij : i = j
            · subst j
              cases i using Fin.lastCases with
              | last =>
                  refine ⟨∏ r : Fin m,
                    MvPolynomial.X (Sum.inr (ULift.up r)), ?_⟩
                  intro x
                  change slPointMatrix (m + 1) (diagonalPoint x)
                    (Fin.last m) (Fin.last m) = _
                  rw [diagonalPoint_matrix]
                  simp [diagonalEntry, dPointEntryInv, evalPolynomial]
              | cast i =>
                  refine ⟨MvPolynomial.X (Sum.inl (ULift.up i)), ?_⟩
                  intro x
                  change slPointMatrix (m + 1) (diagonalPoint x)
                    i.castSucc i.castSucc = _
                  rw [diagonalPoint_matrix]
                  simp [diagonalEntry, dPointEntry, evalPolynomial]
            · refine ⟨0, ?_⟩
              intro x
              change slPointMatrix (m + 1) (diagonalPoint x) i j = _
              rw [diagonalPoint_matrix]
              simp [hij, evalPolynomial] }
      map_one := by
        apply (slPointEquiv (m + 1)).injective
        apply Subtype.ext
        change slPointMatrix (m + 1) (diagonalPoint 1) = 1
        rw [diagonalPoint_matrix]
        ext i j
        by_cases hij : i = j
        · subst j
          cases i using Fin.lastCases with
          | last =>
              simp only [Matrix.diagonal_apply_eq, diagonalEntry,
                Fin.snoc_last, Matrix.one_apply_eq]
              apply Finset.prod_eq_one
              intro i _
              have hi := congrFun (dPointEquiv_one (k := k) m) i
              simpa [dPointEntryInv, dPointEquiv] using
                congrArg (fun u : kˣ => (↑(u⁻¹) : k)) hi
          | cast i =>
              have hi := congrFun (dPointEquiv_one (k := k) m) i
              simpa [diagonalEntry, dPointEntry, dPointEquiv] using
                congrArg Units.val hi
        · simp [hij]
      map_mul := by
        intro x y
        have hentry : diagonalEntry (x * y) =
            diagonalEntry x * diagonalEntry y := by
          funext i
          cases i using Fin.lastCases with
          | last =>
              simp only [diagonalEntry, Fin.snoc_last, Pi.mul_apply]
              change (∏ r : Fin m, (x * y).val (Sum.inr (ULift.up r))) = _
              simp_rw [dPoint_mul_apply]
              exact Finset.prod_mul_distrib
          | cast i =>
              simp only [diagonalEntry, Fin.snoc_castSucc, Pi.mul_apply]
              change (x * y).val (Sum.inl (ULift.up i)) = _
              exact dPoint_mul_apply m x y (Sum.inl (ULift.up i))
        apply (slPointEquiv (m + 1)).injective
        apply Subtype.ext
        change slPointMatrix (m + 1) (diagonalPoint (x * y)) =
          slPointMatrix (m + 1) (diagonalPoint x) *
            slPointMatrix (m + 1) (diagonalPoint y)
        rw [diagonalPoint_matrix, diagonalPoint_matrix, diagonalPoint_matrix]
        ext i j
        rw [Matrix.diagonal_mul]
        by_cases hij : i = j
        · subst j
          simpa [Matrix.diagonal_apply] using congrFun hentry i
        · simp [hij] }
  let T : ClosedSubgroup (slVariety k (m + 1)) :=
    diagonalMorphism.imageClosedSubgroup
  have hcarrier (g : Variety.Point (slVariety k (m + 1))) :
      g ∈ T ↔ ∀ i j : Fin (m + 1), i ≠ j →
        slPointMatrix (m + 1) g i j = 0 := by
    constructor
    · intro hg i j hij
      change g ∈ Set.range diagonalMorphism.onPoints at hg
      obtain ⟨x, hx⟩ := hg
      rw [← hx]
      change slPointMatrix (m + 1) (diagonalPoint x) i j = 0
      rw [diagonalPoint_matrix]
      simp [hij]
    · intro hg
      let A := slPointMatrix (m + 1) g
      have hA : A = Matrix.diagonal (fun i => A i i) := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [A]
        · simp [hij, A, hg i j hij]
      have hprod : ∏ i : Fin (m + 1), A i i = 1 := by
        have hdet := slPoint_det_eq_one (m + 1) g
        change A.det = 1 at hdet
        rw [hA, Matrix.det_diagonal] at hdet
        exact hdet
      have hdiag_ne (i : Fin (m + 1)) : A i i ≠ 0 := by
        intro hi
        have hzero : ∏ j : Fin (m + 1), A j j = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) hi
        rw [hprod] at hzero
        exact one_ne_zero hzero
      let a : Fin m → kˣ := fun i => Units.mk0 (A i.castSucc i.castSucc)
        (hdiag_ne i.castSucc)
      let x : Variety.Point (dVariety k m) := (dPointEquiv m).symm a
      have hxmatrix : slPointMatrix (m + 1) (diagonalPoint x) = A := by
        rw [diagonalPoint_matrix, hA]
        congr 1
        funext i
        cases i using Fin.lastCases with
        | cast i =>
            simp [diagonalEntry, x, a, dPointEquiv_symm_val_inl,
              dPointEntry]
        | last =>
            rw [Fin.prod_univ_castSucc] at hprod
            have hlast : A (Fin.last m) (Fin.last m) =
                (∏ i : Fin m, A i.castSucc i.castSucc)⁻¹ :=
              eq_inv_of_mul_eq_one_right hprod
            simp only [diagonalEntry, Fin.snoc_last]
            rw [show (∏ i : Fin m, dPointEntryInv m x i) =
                (∏ i : Fin m, A i.castSucc i.castSucc)⁻¹ by
              simp [x, a, dPointEntryInv, dPointEquiv_symm_val_inr,
                Finset.prod_inv_distrib]]
            exact hlast.symm
      change g ∈ Set.range diagonalMorphism.onPoints
      refine ⟨x, ?_⟩
      apply (slPointEquiv (m + 1)).injective
      apply Subtype.ext
      exact hxmatrix
  have hTtorus : IsSubtorus T :=
    morphism_image_isTorus diagonalMorphism (dVariety_isTorus m)
  have hTmax : IsMaximalTorus T := by
    refine ⟨hTtorus, ?_⟩
    intro S hStorus hTS
    let : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
    apply SetLike.coe_injective
    apply Set.Subset.antisymm
    · intro g hg
      apply (hcarrier g).2
      intro i j hij
      obtain ⟨a, ha⟩ := exists_unit_zpow_ne_one (k := k)
        (z := (2 : ℤ)) (by norm_num)
      have ha_ne_inv : a ≠ a⁻¹ := by
        intro hai
        apply ha
        calc
          a ^ (2 : ℤ) = a ^ (2 : ℕ) := zpow_ofNat a 2
          _ = a * a := pow_two a
          _ = a⁻¹ * a := congrArg (fun z : kˣ => z * a) hai
          _ = 1 := inv_mul_cancel a
      let dUnit : Fin (m + 1) → kˣ := fun r =>
        if r = i then a else if r = j then a⁻¹ else 1
      have hdUnit_factor : dUnit = fun r =>
          (if r = i then a else 1) * (if r = j then a⁻¹ else 1) := by
        funext r
        by_cases hri : r = i
        · subst r
          simp [dUnit, hij]
        · by_cases hrj : r = j
          · subst r
            simp [dUnit, hri]
          · simp [dUnit, hri, hrj]
      have hdUnit_prod : ∏ r : Fin (m + 1), dUnit r = 1 := by
        rw [hdUnit_factor, Finset.prod_mul_distrib,
          Fintype.prod_ite_eq', Fintype.prod_ite_eq']
        simp
      let d : Fin (m + 1) → k := fun r => (dUnit r : k)
      have hdprod : ∏ r : Fin (m + 1), d r = 1 := by
        simpa [d] using congrArg Units.val hdUnit_prod
      let t : Variety.Point (slVariety k (m + 1)) :=
        (slPointEquiv (m + 1)).symm
          ⟨Matrix.diagonal d, by rw [Matrix.det_diagonal, hdprod]⟩
      have htMatrix : slPointMatrix (m + 1) t = Matrix.diagonal d := by
        change ((slPointEquiv (m + 1)) t).1 = _
        exact congrArg Subtype.val ((slPointEquiv (m + 1)).apply_symm_apply _)
      have htT : t ∈ T := by
        apply (hcarrier t).2
        intro p q hpq
        rw [htMatrix]
        simp [hpq]
      have htS : t ∈ S := hTS htT
      let gS : Variety.Point S.carrierVariety :=
        S.pointEquiv.symm ⟨g, hg⟩
      let tS : Variety.Point S.carrierVariety :=
        S.pointEquiv.symm ⟨t, htS⟩
      have hgSval : S.inclusion.onPoints gS = g := by
        change (S.pointEquiv gS).val = g
        dsimp [gS]
        rw [S.pointEquiv.apply_symm_apply]
      have htSval : S.inclusion.onPoints tS = t := by
        change (S.pointEquiv tS).val = t
        dsimp [tS]
        rw [S.pointEquiv.apply_symm_apply]
      have hcommS := hStorus.isMulCommutative
      rw [isMulCommutative_iff] at hcommS
      have hcomm := congrArg S.inclusion.onPoints (hcommS gS tS)
      rw [map_mul, map_mul, hgSval, htSval] at hcomm
      have hmatrix := congrArg (slPointMatrix (m + 1)) hcomm
      let A := slPointMatrix (m + 1) g
      change A * slPointMatrix (m + 1) t =
        slPointMatrix (m + 1) t * A at hmatrix
      rw [htMatrix] at hmatrix
      have hentry := congrFun (congrFun hmatrix i) j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
      have hdne : d i ≠ d j := by
        intro hd
        apply ha_ne_inv
        apply Units.ext
        simpa [d, dUnit, hij, hij.symm] using hd
      have hzero : (d j - d i) * A i j = 0 := by
        rw [sub_mul, mul_comm (d j) (A i j), hentry, sub_self]
      exact (mul_eq_zero.mp hzero).resolve_left
        (sub_ne_zero.mpr hdne.symm)
    · exact hTS
  exact ⟨T, hTmax, hcarrier⟩

end Theory.AlgebraicGroup
