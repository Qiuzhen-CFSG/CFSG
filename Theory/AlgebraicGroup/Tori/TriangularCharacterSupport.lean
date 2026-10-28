module

public import Theory.AlgebraicGroup.Representations.Triangular
public import Theory.AlgebraicGroup.Tori.Character.Algebra
public import Theory.AlgebraicGroup.Tori.Semisimple

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Every character occurring in a matrix coefficient of a torus morphism to
an upper-triangular group comes by pullback from the diagonal torus. -/
public theorem triangularMorphism_characterSupport_subset_diagonalPullback
    {T : Variety k} [AlgebraicGroup T]
    (hT : IsTorus T) (n : ℕ)
    (f : AlgebraicGroup.Morphism T (tVariety k n))
    (i j : Fin n) :
    let eT := torusCharacterAlgebraEquiv T
      hT.isMulCommutative (IsTorus.all_semisimple hT)
    let c := f.toVariety.pullbackRingHom
      (triangularMatrixCoordinate (k := k) n i j)
    ((eT.symm c).coeff.support : Set (TorusCharacter T)) ⊆
      Set.range (TorusCharacter.pullback ((tDiagonalMorphism n).comp f)) := by
  classical
  dsimp only
  let eT := torusCharacterAlgebraEquiv T
    hT.isMulCommutative (IsTorus.all_semisimple hT)
  let c : Fin n → Fin n → Variety.PolynomialFunction T := fun r s =>
    f.toVariety.pullbackRingHom
      (triangularMatrixCoordinate (k := k) n r s)
  let b : Fin n → Fin n → MonoidAlgebra k (TorusCharacter T) :=
    fun r s => eT.symm (c r s)
  let δ := (tDiagonalMorphism n).comp f
  let diagonalCharacter : Fin n → TorusCharacter T := fun r =>
    TorusCharacter.pullback δ (dCoordinateCharacter n r)
  have hb (r s : Fin n) : eT (b r s) = c r s := by
    exact eT.apply_symm_apply (c r s)
  have hsingle (χ : TorusCharacter T) (a : k) :
      eT (MonoidAlgebra.single χ a) =
        a • χ.scalarPolynomialFunction := by
    change
      ((MonoidAlgebra.lift k (Variety.PolynomialFunction T) (TorusCharacter T))
        (TorusCharacter.scalarPolynomialFunctionMonoidHom T)
        (MonoidAlgebra.single χ a)) = _
    rw [MonoidAlgebra.lift_single]
    rfl
  have heval (r s : Fin n) (x : Variety.Point T) :
      c r s x =
        (b r s).coeff.sum
          (fun χ a => a * χ.pointCharacter x) := by
    rw [← hb r s]
    calc
      (eT (b r s)) x =
          (eT ((b r s).coeff.sum
            fun χ a => MonoidAlgebra.single χ a)) x := by
        rw [MonoidAlgebra.sum_coeff_single]
      _ = (b r s).coeff.sum
          (fun χ a => a * χ.pointCharacter x) := by
        rw [map_finsuppSum]
        change polynomialFunctionEvalAddHom T x
            ((b r s).coeff.sum
              (fun χ a => eT (MonoidAlgebra.single χ a))) = _
        rw [map_finsuppSum]
        apply Finsupp.sum_congr
        intro χ hχ
        rw [hsingle]
        change ((b r s).coeff χ • χ.scalarPolynomialFunction) x = _
        rw [polynomialFunction_smul_apply,
          TorusCharacter.scalarPolynomialFunction_apply]
  have hmul (r s : Fin n) (x y : Variety.Point T) :
      c r s (x * y) = ∑ l, c r l x * c l s y := by
    dsimp only [c]
    change evalPolynomial (f.onPoints (x * y)).val
        (MvPolynomial.X (Sum.inl (ULift.up (r, s)))) =
      ∑ l,
        evalPolynomial (f.onPoints x).val
            (MvPolynomial.X (Sum.inl (ULift.up (r, l)))) *
          evalPolynomial (f.onPoints y).val
            (MvPolynomial.X (Sum.inl (ULift.up (l, s))))
    simp only [evalPolynomial_X]
    rw [map_mul]
    change (tPointEquiv k n (f.onPoints x * f.onPoints y)).1.1 r s =
      ∑ l, (tPointEquiv k n (f.onPoints x)).1.1 r l *
        (tPointEquiv k n (f.onPoints y)).1.1 l s
    have hrs := congrArg (fun A : tTriangularGL k n => A.1.1 r s)
      (tPointEquiv_mul n (f.onPoints x) (f.onPoints y))
    simpa [Matrix.mul_apply] using hrs
  have hdiagonal (r : Fin n) :
      c r r = (diagonalCharacter r).scalarPolynomialFunction := by
    apply Variety.PolynomialFunction.ext
    intro x
    rw [TorusCharacter.scalarPolynomialFunction_apply]
    dsimp only [c]
    change evalPolynomial (f.onPoints x).val
        (MvPolynomial.X (Sum.inl (ULift.up (r, r)))) = _
    rw [evalPolynomial_X]
    have hd := dCoordinateCharacter_apply n r (δ.onPoints x)
    change dPointEquiv 1
        ((dCoordinateCharacter n r).onPoints
          ((tDiagonalMorphism n).onPoints (f.onPoints x))) 0 =
      dPointEquiv n ((tDiagonalMorphism n).onPoints (f.onPoints x)) r at hd
    change (f.onPoints x).val (Sum.inl (ULift.up (r, r))) =
      dPointEquiv 1
        ((dCoordinateCharacter n r).onPoints
          ((tDiagonalMorphism n).onPoints (f.onPoints x))) 0
    rw [hd]
    change (f.onPoints x).val (Sum.inl (ULift.up (r, r))) =
      ↑(tDiagonalHom n (tPointEquiv k n (f.onPoints x)) r)
    simpa only [tPointMatrix] using
      (tDiagonalHom_val n (f.onPoints x) r).symm
  have hbelow {r s : Fin n} (hsr : s < r) (x : Variety.Point T) :
      c r s x = 0 := by
    dsimp only [c]
    change evalPolynomial (f.onPoints x).val
        (MvPolynomial.X (Sum.inl (ULift.up (r, s)))) = 0
    rw [evalPolynomial_X]
    exact tPoint_triangular n (f.onPoints x) hsr
  have hcoefficient (r s : Fin n) (χ : TorusCharacter T)
      (y : Variety.Point T) :
      (b r s).coeff χ * χ.pointCharacter y =
        ∑ l, c l s y * (b r l).coeff χ := by
    let L : MonoidAlgebra k (TorusCharacter T) :=
      (b r s).coeff.sum fun η a =>
        MonoidAlgebra.single η (a * η.pointCharacter y)
    let R : MonoidAlgebra k (TorusCharacter T) :=
      ∑ l, (c l s y) • b r l
    have hLR : L = R := by
      apply eT.injective
      apply Variety.PolynomialFunction.ext
      intro x
      calc
        (eT L) x = (b r s).coeff.sum (fun η a =>
            (a * η.pointCharacter y) * η.pointCharacter x) := by
          dsimp only [L]
          rw [map_finsuppSum]
          change polynomialFunctionEvalAddHom T x
              ((b r s).coeff.sum (fun η a =>
                eT (MonoidAlgebra.single η
                  (a * η.pointCharacter y)))) = _
          rw [map_finsuppSum]
          apply Finsupp.sum_congr
          intro η hη
          rw [hsingle]
          change (((b r s).coeff η * η.pointCharacter y) •
            η.scalarPolynomialFunction) x = _
          rw [polynomialFunction_smul_apply,
            TorusCharacter.scalarPolynomialFunction_apply]
        _ = (b r s).coeff.sum (fun η a =>
            a * η.pointCharacter (x * y)) := by
          apply Finsupp.sum_congr
          intro η hη
          rw [map_mul]
          ring
        _ = c r s (x * y) := (heval r s (x * y)).symm
        _ = ∑ l, c r l x * c l s y := hmul r s x y
        _ = (eT R) x := by
          symm
          dsimp only [R]
          rw [map_sum]
          change polynomialFunctionEvalAddHom T x
            (∑ l, eT ((c l s y) • b r l)) = _
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro l hl
          rw [map_smul]
          change (((c l s y) • eT (b r l)) :
            Variety.PolynomialFunction T) x = _
          rw [polynomialFunction_smul_apply, hb]
          ring
    let ev : MonoidAlgebra k (TorusCharacter T) →+ k :=
      { toFun := fun q => q.coeff χ
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hcoeff := congrArg ev hLR
    have hLcoeff : ev L = (b r s).coeff χ * χ.pointCharacter y := by
      dsimp only [L]
      rw [map_finsuppSum]
      by_cases hχ : χ ∈ (b r s).coeff.support
      · rw [Finsupp.sum, Finset.sum_eq_single χ]
        · change (Finsupp.single χ
              ((b r s).coeff χ * χ.pointCharacter y)) χ = _
          rw [Finsupp.single_eq_same]
        · intro η hηs hηχ
          change (Finsupp.single η
              ((b r s).coeff η * η.pointCharacter y)) χ = 0
          rw [Finsupp.single_eq_of_ne (Ne.symm hηχ)]
        · intro hχ'
          exact (hχ' hχ).elim
      · have hz : (b r s).coeff χ = 0 :=
          Finsupp.notMem_support_iff.mp hχ
        rw [Finsupp.sum]
        have hzero : ∀ η ∈ (b r s).coeff.support,
            ev (MonoidAlgebra.single η
              ((b r s).coeff η * η.pointCharacter y)) = 0 := by
          intro η hη
          have hηχ : η ≠ χ := by
            intro h
            subst η
            exact hχ hη
          change (Finsupp.single η
              ((b r s).coeff η * η.pointCharacter y)) χ = 0
          rw [Finsupp.single_eq_of_ne (Ne.symm hηχ)]
        rw [Finset.sum_eq_zero hzero, hz, zero_mul]
    have hRcoeff : ev R =
        ∑ l, c l s y * (b r l).coeff χ := by
      dsimp only [R]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro l hl
      change ((c l s y) • b r l).coeff χ = _
      rfl
    rw [hLcoeff, hRcoeff] at hcoeff
    exact hcoeff
  have hind : ∀ m : ℕ, ∀ s : Fin n, s.val = m →
      ∀ r : Fin n, ∀ χ : TorusCharacter T,
        χ ∈ (b r s).coeff.support → χ ∈ Set.range (TorusCharacter.pullback δ) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro s hs r χ hχsupport
        by_contra hχrange
        have hχne : (b r s).coeff χ ≠ 0 :=
          Finsupp.mem_support_iff.mp hχsupport
        have hsum (y : Variety.Point T) :
            (∑ l, c l s y * (b r l).coeff χ) =
              c s s y * (b r s).coeff χ := by
          apply Finset.sum_eq_single s
          · intro l hl hls
            rcases lt_or_gt_of_ne hls with hlt | hgt
            · have hlm : l.val < m := by omega
              have hzero : (b r l).coeff χ = 0 := by
                by_contra hne
                have hmem : χ ∈ (b r l).coeff.support :=
                  Finsupp.mem_support_iff.mpr hne
                exact hχrange (ih l.val hlm l rfl r χ hmem)
              rw [hzero, mul_zero]
            · rw [hbelow hgt y, zero_mul]
          · intro hsnot
            exact (hsnot (Finset.mem_univ s)).elim
        have hpoint (y : Variety.Point T) :
            χ.pointCharacter y = (diagonalCharacter s).pointCharacter y := by
          have hc := hcoefficient r s χ y
          rw [hsum y] at hc
          have hd := congrArg (fun q : Variety.PolynomialFunction T => q y)
            (hdiagonal s)
          rw [TorusCharacter.scalarPolynomialFunction_apply] at hd
          apply mul_left_cancel₀ hχne
          calc
            (b r s).coeff χ * χ.pointCharacter y =
                c s s y * (b r s).coeff χ := hc
            _ = (b r s).coeff χ * c s s y := mul_comm _ _
            _ = (b r s).coeff χ *
                (diagonalCharacter s).pointCharacter y := by rw [hd]
        have hχdiag : χ = diagonalCharacter s := by
          apply TorusCharacter.pointCharacter_injective
          ext y
          exact hpoint y
        apply hχrange
        refine ⟨dCoordinateCharacter n s, ?_⟩
        exact hχdiag.symm
  change ((b i j).coeff.support : Set (TorusCharacter T)) ⊆
    Set.range (TorusCharacter.pullback δ)
  intro χ hχ
  exact hind j.val j rfl i χ hχ

end Theory.AlgebraicGroup
