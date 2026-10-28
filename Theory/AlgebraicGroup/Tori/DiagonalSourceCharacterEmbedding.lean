module

public import Theory.AlgebraicGroup.Tori.Maximal.theorem_1_4_3_b

/-!
This module constructs a diagonal-group morphism from any algebraic group that
is a point-surjective image of a diagonal group, and proves that its pullback on
polynomial functions is surjective.

The proof first identifies the polynomial functions on `D_n` with the Laurent
group algebra on `ℤ^n`, using independence of distinct characters and the
ambient coordinate functions and their inverses. The Hopf comultiplication then
extracts every Laurent character occurring in the pullback image. Characters
in the finite union of the supports of the target coordinates, together with
their inverses, descend through the given morphism and define the required map
to a finite diagonal group. Expanding each target coordinate in this Laurent
basis proves that every polynomial function lies in the new pullback image.

This is the staged proof for
`ag-tori-diagonal-source-character-embedding`, using only its strict ancestor
coordinate-ring and algebraic-group interfaces.
-/

set_option warningAsError false

namespace Theory.AlgebraicGroup

public theorem Morphism.exists_diagonal_morphism_with_surjective_pullback_of_surjective_from_dVariety
    {k : Type*} [Field k] [IsAlgClosed k]
    {n : ℕ} {H : Variety k} [AlgebraicGroup H]
    (f : Morphism (dVariety k n) H)
    (hf : Function.Surjective f.onPoints) :
    ∃ m : ℕ, ∃ j : Morphism H (dVariety k m),
      Function.Surjective j.toVariety.pullbackRingHom := by
  classical
  let D := dVariety k n
  let A := Variety.PolynomialFunction D
  let coordinateUnit : Fin n → Aˣ := fun i =>
    { val := Variety.PolynomialFunction.ofPolynomial D
        (MvPolynomial.X (Sum.inl (ULift.up i)))
      inv := Variety.PolynomialFunction.ofPolynomial D
        (MvPolynomial.X (Sum.inr (ULift.up i)))
      val_inv := by
        apply Variety.PolynomialFunction.ext
        intro x
        rw [polynomialFunction_mul_apply]
        change evalPolynomial x.val (MvPolynomial.X (Sum.inl (ULift.up i))) *
          evalPolynomial x.val (MvPolynomial.X (Sum.inr (ULift.up i))) = 1
        rw [evalPolynomial_X, evalPolynomial_X]
        exact dPoint_entry_mul_inv n x i
      inv_val := by
        apply Variety.PolynomialFunction.ext
        intro x
        rw [polynomialFunction_mul_apply]
        change evalPolynomial x.val (MvPolynomial.X (Sum.inr (ULift.up i))) *
          evalPolynomial x.val (MvPolynomial.X (Sum.inl (ULift.up i))) = 1
        rw [evalPolynomial_X, evalPolynomial_X, mul_comm]
        exact dPoint_entry_mul_inv n x i }
  let character : Multiplicative (Fin n → ℤ) →* A :=
    {
    toFun z := (↑(∏ i, coordinateUnit i ^ z.toAdd i) : A)
    map_one' := by
      simp
    map_mul' := by
      intro z w
      change (↑(∏ i, coordinateUnit i ^ (z.toAdd i + w.toAdd i)) : A) =
        (↑(∏ i, coordinateUnit i ^ z.toAdd i) : A) *
          (↑(∏ i, coordinateUnit i ^ w.toAdd i) : A)
      simp_rw [zpow_add]
      rw [Finset.prod_mul_distrib]
      rfl }
  let laurent : AddMonoidAlgebra k (Fin n → ℤ) →ₐ[k] A :=
    AddMonoidAlgebra.lift k A (Fin n → ℤ) character
  let pointCharacter (z : Fin n → ℤ) : Variety.Point D →* k :=
    {
    toFun x := (↑(∏ i, (dPointEquiv n x i) ^ z i) : k)
    map_one' := by
      have hone := dPointEquiv_one (k := k) n
      have hu : (∏ i, (dPointEquiv n (1 : Variety.Point D) i) ^ z i) =
          (1 : kˣ) := by
        apply Finset.prod_eq_one
        intro i _hi
        rw [congrFun hone i]
        exact one_zpow (z i)
      exact congrArg Units.val hu
    map_mul' := by
      intro x y
      have hmul := dPointEquiv_mul n x y
      have hu : (∏ i, (dPointEquiv n (x * y) i) ^ z i) =
          (∏ i, (dPointEquiv n x i) ^ z i) *
            ∏ i, (dPointEquiv n y i) ^ z i := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i _hi
        rw [congrFun hmul i, Pi.mul_apply, mul_zpow]
      exact congrArg Units.val hu }
  have character_apply (z : Fin n → ℤ) (x : Variety.Point D) :
      character (Multiplicative.ofAdd z) x = pointCharacter z x := by
    change ((↑(∏ i, coordinateUnit i ^ z i) : A) : Variety.Point D → k) x =
      (↑(∏ i, (dPointEquiv n x i) ^ z i) : k)
    let ev : A →+* k :=
      { toFun := fun q => q x
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change ev (↑(∏ i, coordinateUnit i ^ z i) : A) =
      (↑(∏ i, (dPointEquiv n x i) ^ z i) : k)
    have hu : (∏ i, coordinateUnit i ^ z i).map ev =
        ∏ i, (dPointEquiv n x i) ^ z i := by
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro i _hi
      calc
        (coordinateUnit i ^ z i).map ev.toMonoidHom =
            (coordinateUnit i).map ev.toMonoidHom ^ z i :=
          _root_.map_zpow (Units.map ev.toMonoidHom) (coordinateUnit i) (z i)
        _ = (dPointEquiv n x i) ^ z i := by
          congr 1
          apply Units.ext
          change evalPolynomial x.val
            (MvPolynomial.X (Sum.inl (ULift.up i))) =
              (dPointEquiv n x i).val
          rw [evalPolynomial_X]
          rfl
    exact congrArg Units.val hu
  have pointCharacter_injective : Function.Injective pointCharacter := by
    intro z w hzw
    funext i
    by_contra hne
    have hdiff : z i - w i ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨a, ha⟩ := exists_unit_zpow_ne_one (k := k) hdiff
    let u : Fin n → kˣ := fun q => if q = i then a else 1
    let x : Variety.Point D := (dPointEquiv n).symm u
    have hx (q : Fin n) : dPointEquiv n x q = u q := by
      exact congrFun ((dPointEquiv n).apply_symm_apply u) q
    have hprod (v : Fin n → ℤ) :
        ∏ q, (dPointEquiv n x q) ^ v q = a ^ v i := by
      calc
        ∏ q, (dPointEquiv n x q) ^ v q =
            ∏ q, (if q = i then a else 1) ^ v q := by
          apply Finset.prod_congr rfl
          intro q _hq
          rw [hx]
        _ = a ^ v i := by simp
    have heval := congrArg (fun g : Variety.Point D →* k => g x) hzw
    change (↑(∏ q, (dPointEquiv n x q) ^ z q) : k) =
      (↑(∏ q, (dPointEquiv n x q) ^ w q) : k) at heval
    rw [hprod z, hprod w] at heval
    have hpowers : a ^ z i = a ^ w i := Units.val_injective heval
    apply ha
    rw [zpow_sub, hpowers]
    exact mul_inv_cancel _
  have character_linearIndependent : LinearIndependent k
      (fun z : Fin n → ℤ => character (Multiplicative.ofAdd z)) := by
    let coeLinear : A →ₗ[k] (Variety.Point D → k) :=
      { toFun := fun q x => q x
        map_add' := fun _ _ => rfl
        map_smul' := by
          intro c q
          funext x
          exact polynomialFunction_smul_apply D c q x }
    apply LinearIndependent.of_comp coeLinear
    rw [show (coeLinear ∘ fun z : Fin n → ℤ =>
        character (Multiplicative.ofAdd z)) =
        (fun z : Fin n → ℤ => (pointCharacter z : Variety.Point D → k)) by
      funext z x
      exact character_apply z x]
    exact (linearIndependent_monoidHom (Variety.Point D) k).comp
      pointCharacter pointCharacter_injective
  have laurent_injective : Function.Injective laurent := by
    intro q r hqr
    change Function.Injective (Finsupp.linearCombination k
      (fun z : Fin n → ℤ => character (Multiplicative.ofAdd z))) at character_linearIndependent
    apply AddMonoidAlgebra.coeff_injective
    apply character_linearIndependent
    change AddMonoidAlgebra.lift k A (Fin n → ℤ) character q =
      AddMonoidAlgebra.lift k A (Fin n → ℤ) character r at hqr
    change q.coeff.sum (fun a b => b • character (Multiplicative.ofAdd a)) =
      r.coeff.sum (fun a b => b • character (Multiplicative.ofAdd a)) at hqr
    exact hqr
  let preCoordinate : D.Coordinates → AddMonoidAlgebra k (Fin n → ℤ) := fun c =>
    match c with
    | Sum.inl i => AddMonoidAlgebra.single (Pi.single i.down 1) 1
    | Sum.inr i =>
        AddMonoidAlgebra.single
          (-(Pi.single i.down (1 : ℤ) : Fin n → ℤ)) 1
  let preEvaluation : MvPolynomial D.Coordinates k →ₐ[k]
      AddMonoidAlgebra k (Fin n → ℤ) :=
    MvPolynomial.aeval preCoordinate
  have laurent_preEvaluation : laurent.comp preEvaluation = evaluationAlgHom D := by
    apply MvPolynomial.algHom_ext
    intro c
    cases c with
    | inl i =>
        rw [AlgHom.comp_apply, MvPolynomial.aeval_X,
          AddMonoidAlgebra.lift_single]
        rw [one_smul]
        change (↑(∏ q, coordinateUnit q ^ (Pi.single i.down 1) q) : A) =
          Variety.PolynomialFunction.ofPolynomial D
            (MvPolynomial.X (Sum.inl i))
        rw [Finset.prod_eq_single i.down]
        · simp [Pi.single, coordinateUnit]
        · intro q _hq hqi
          simp [Pi.single, hqi]
        · intro h
          exact (h (Finset.mem_univ i.down)).elim
    | inr i =>
        rw [AlgHom.comp_apply, MvPolynomial.aeval_X,
          AddMonoidAlgebra.lift_single]
        rw [one_smul]
        change (↑(∏ q, coordinateUnit q ^
          (-(Pi.single i.down (1 : ℤ) : Fin n → ℤ)) q) : A) =
          Variety.PolynomialFunction.ofPolynomial D
            (MvPolynomial.X (Sum.inr i))
        rw [Finset.prod_eq_single i.down]
        · simp [Pi.single, coordinateUnit]
        · intro q _hq hqi
          simp [Pi.single, hqi]
        · intro h
          exact (h (Finset.mem_univ i.down)).elim
  have laurent_surjective : Function.Surjective laurent := by
    intro q
    rcases q.representedBy with ⟨p, hp⟩
    refine ⟨preEvaluation p, ?_⟩
    rw [show laurent (preEvaluation p) = evaluationAlgHom D p by
      exact DFunLike.congr_fun laurent_preEvaluation p]
    apply Variety.PolynomialFunction.ext
    intro x
    exact (hp x).symm
  let laurentEquiv : AddMonoidAlgebra k (Fin n → ℤ) ≃ₐ[k] A :=
    AlgEquiv.ofBijective laurent ⟨laurent_injective, laurent_surjective⟩
  let B := Variety.PolynomialFunction H
  let pull : B →ₐ[k] A := f.toVariety.pullbackAlgHom
  have pull_injective : Function.Injective pull := by
    intro q r hqr
    apply Variety.PolynomialFunction.ext
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact congrArg (fun a : A => a x) hqr
  let inclusion : B →ₐ[k] AddMonoidAlgebra k (Fin n → ℤ) :=
    laurentEquiv.symm.toAlgHom.comp pull
  have inclusion_apply (q : B) : laurentEquiv (inclusion q) = pull q := by
    exact laurentEquiv.apply_symm_apply (pull q)
  have inclusion_injective : Function.Injective inclusion :=
    laurentEquiv.symm.injective.comp pull_injective
  let tensorLaurentEquiv :
      TensorProduct k (AddMonoidAlgebra k (Fin n → ℤ))
          (AddMonoidAlgebra k (Fin n → ℤ)) ≃ₐ[k]
        Variety.PolynomialFunction (Variety.prod D D) :=
    (Algebra.TensorProduct.congr laurentEquiv laurentEquiv).trans
      (polynomialFunction_prod_algEquiv D D)
  have tensorLaurentEquiv_tmul_apply
      (a b : AddMonoidAlgebra k (Fin n → ℤ))
      (x : Variety.Point D) (y : Variety.Point D) :
      tensorLaurentEquiv (a ⊗ₜ[k] b)
          ((Variety.prodPointEquiv D D).symm (x, y)) =
        laurentEquiv a x * laurentEquiv b y := by
    change polynomialFunctionTensor D D
        (laurentEquiv a ⊗ₜ[k] laurentEquiv b)
          ((Variety.prodPointEquiv D D).symm (x, y)) = _
    rw [polynomialFunctionTensor_tmul, polynomialFunction_mul_apply,
      polynomialFunctionLeft_apply, polynomialFunctionRight_apply,
      (Variety.prodPointEquiv D D).apply_symm_apply]
  let diagonalTensor : AddMonoidAlgebra k (Fin n → ℤ) →ₗ[k]
      TensorProduct k (AddMonoidAlgebra k (Fin n → ℤ))
        (AddMonoidAlgebra k (Fin n → ℤ)) :=
    (Finsupp.linearCombination k (fun z : Fin n → ℤ =>
      AddMonoidAlgebra.single z 1 ⊗ₜ[k]
        AddMonoidAlgebra.single z 1)).comp
      (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap
  have diagonalTensor_single (z : Fin n → ℤ) (c : k) :
      diagonalTensor (AddMonoidAlgebra.single z c) =
        c • (AddMonoidAlgebra.single z 1 ⊗ₜ[k]
          AddMonoidAlgebra.single z 1) := by
    simp [diagonalTensor]
  have laurentEquiv_single (z : Fin n → ℤ) (c : k) :
      laurentEquiv (AddMonoidAlgebra.single z c) =
        c • character (Multiplicative.ofAdd z) := by
    exact AddMonoidAlgebra.lift_single character z c
  have diagonalTensor_apply
      (q : AddMonoidAlgebra k (Fin n → ℤ))
      (x y : Variety.Point D) :
      tensorLaurentEquiv (diagonalTensor q)
          ((Variety.prodPointEquiv D D).symm (x, y)) =
        laurentEquiv q (x * y) := by
    induction q using AddMonoidAlgebra.induction_linear with
    | zero => simp [map_zero]
    | add a b ha hb =>
        rw [map_add, map_add, map_add]
        rw [show (tensorLaurentEquiv (diagonalTensor a) +
              tensorLaurentEquiv (diagonalTensor b))
              ((Variety.prodPointEquiv D D).symm (x, y)) =
            tensorLaurentEquiv (diagonalTensor a)
                ((Variety.prodPointEquiv D D).symm (x, y)) +
              tensorLaurentEquiv (diagonalTensor b)
                ((Variety.prodPointEquiv D D).symm (x, y)) by rfl]
        rw [show (laurentEquiv a + laurentEquiv b) (x * y) =
            laurentEquiv a (x * y) + laurentEquiv b (x * y) by rfl]
        rw [ha, hb]
    | single z c =>
        rw [diagonalTensor_single, map_smul,
          polynomialFunction_smul_apply,
          tensorLaurentEquiv_tmul_apply,
          laurentEquiv_single, polynomialFunction_smul_apply,
          laurentEquiv_single]
        rw [one_smul, one_mul,
          polynomialFunction_smul_apply D c
            (character (Multiplicative.ofAdd z)) (x * y),
          character_apply z x, character_apply z y,
          character_apply z (x * y)]
        rw [(pointCharacter z).map_mul]
  let comultiplication (q : B) : TensorProduct k B B :=
    (polynomialFunction_prod_algEquiv H H).symm
      ((AlgebraicGroup.mulMorphism H).pullbackAlgHom q)
  have inclusionTensor_apply (t : TensorProduct k B B)
      (x y : Variety.Point D) :
      tensorLaurentEquiv
          (TensorProduct.map inclusion.toLinearMap inclusion.toLinearMap t)
          ((Variety.prodPointEquiv D D).symm (x, y)) =
        polynomialFunction_prod_algEquiv H H t
          ((Variety.prodPointEquiv H H).symm (f.onPoints x, f.onPoints y)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
        simp only [map_add]
        rw [show (tensorLaurentEquiv
                ((TensorProduct.map inclusion.toLinearMap inclusion.toLinearMap) a) +
              tensorLaurentEquiv
                ((TensorProduct.map inclusion.toLinearMap inclusion.toLinearMap) b))
                ((Variety.prodPointEquiv D D).symm (x, y)) =
            tensorLaurentEquiv
                ((TensorProduct.map inclusion.toLinearMap inclusion.toLinearMap) a)
                ((Variety.prodPointEquiv D D).symm (x, y)) +
              tensorLaurentEquiv
                ((TensorProduct.map inclusion.toLinearMap inclusion.toLinearMap) b)
                ((Variety.prodPointEquiv D D).symm (x, y)) by rfl]
        rw [show (polynomialFunction_prod_algEquiv H H a +
              polynomialFunction_prod_algEquiv H H b)
                ((Variety.prodPointEquiv H H).symm
                  (f.onPoints x, f.onPoints y)) =
            polynomialFunction_prod_algEquiv H H a
                ((Variety.prodPointEquiv H H).symm
                  (f.onPoints x, f.onPoints y)) +
              polynomialFunction_prod_algEquiv H H b
                ((Variety.prodPointEquiv H H).symm
                  (f.onPoints x, f.onPoints y)) by rfl]
        exact congrArg₂ (fun u v => u + v) ha hb
    | tmul a b =>
        rw [TensorProduct.map_tmul, tensorLaurentEquiv_tmul_apply]
        change laurentEquiv (inclusion a) x * laurentEquiv (inclusion b) y = _
        rw [inclusion_apply, inclusion_apply]
        change a (f.onPoints x) * b (f.onPoints y) = _
        rw [show polynomialFunction_prod_algEquiv H H (a ⊗ₜ[k] b) =
            polynomialFunctionTensor H H (a ⊗ₜ[k] b) by rfl]
        rw [polynomialFunctionTensor_tmul, polynomialFunction_mul_apply,
          polynomialFunctionLeft_apply, polynomialFunctionRight_apply,
          (Variety.prodPointEquiv H H).apply_symm_apply]
  have diagonalTensor_inclusion (q : B) :
      diagonalTensor (inclusion q) =
        TensorProduct.map inclusion.toLinearMap inclusion.toLinearMap
          (comultiplication q) := by
    apply tensorLaurentEquiv.injective
    apply Variety.PolynomialFunction.ext
    intro xy
    let x := (Variety.prodPointEquiv D D xy).1
    let y := (Variety.prodPointEquiv D D xy).2
    have hxy : (Variety.prodPointEquiv D D).symm (x, y) = xy := by
      exact (Variety.prodPointEquiv D D).symm_apply_apply xy
    rw [← hxy, diagonalTensor_apply, inclusionTensor_apply]
    rw [inclusion_apply]
    change q (f.onPoints (x * y)) =
      polynomialFunction_prod_algEquiv H H (comultiplication q)
        ((Variety.prodPointEquiv H H).symm (f.onPoints x, f.onPoints y))
    rw [show polynomialFunction_prod_algEquiv H H (comultiplication q) =
        (AlgebraicGroup.mulMorphism H).pullbackAlgHom q by
      exact (polynomialFunction_prod_algEquiv H H).apply_symm_apply _]
    change q (f.onPoints (x * y)) = q (f.onPoints x * f.onPoints y)
    exact congrArg (fun y : Variety.Point H => q y) (f.onPoints.map_mul x y)
  let coefficient (z : Fin n → ℤ) :
      AddMonoidAlgebra k (Fin n → ℤ) →ₗ[k] k :=
    { toFun := fun q => q.coeff z
      map_add' := by simp
      map_smul' := by simp }
  let contractLaurent (z : Fin n → ℤ) :
      TensorProduct k (AddMonoidAlgebra k (Fin n → ℤ))
        (AddMonoidAlgebra k (Fin n → ℤ)) →ₗ[k]
          AddMonoidAlgebra k (Fin n → ℤ) :=
    (TensorProduct.rid k (AddMonoidAlgebra k (Fin n → ℤ))).toLinearMap.comp
      (TensorProduct.map LinearMap.id (coefficient z))
  let contractSource (z : Fin n → ℤ) : TensorProduct k B B →ₗ[k] B :=
    (TensorProduct.rid k B).toLinearMap.comp
      (TensorProduct.map LinearMap.id
        ((coefficient z).comp inclusion.toLinearMap))
  have contractLaurent_diagonalTensor
      (z : Fin n → ℤ) (q : AddMonoidAlgebra k (Fin n → ℤ)) :
      contractLaurent z (diagonalTensor q) =
        q.coeff z • AddMonoidAlgebra.single z 1 := by
    induction q using AddMonoidAlgebra.induction_linear with
    | zero => simp [map_zero]
    | add a b ha hb =>
        rw [map_add, map_add, ha, hb]
        change a.coeff z • AddMonoidAlgebra.single z 1 +
            b.coeff z • AddMonoidAlgebra.single z 1 =
          (a.coeff z + b.coeff z) • AddMonoidAlgebra.single z 1
        rw [add_smul]
    | single w c =>
        by_cases hwz : w = z
        · subst w
          simp [diagonalTensor_single, contractLaurent, coefficient]
          change c * (AddMonoidAlgebra.single z 1).coeff z = c
          simp
        · simp [diagonalTensor_single, contractLaurent, coefficient, hwz]
          right
          change (AddMonoidAlgebra.single w 1).coeff z = 0
          simp [hwz]
  have contractLaurent_inclusionTensor (z : Fin n → ℤ)
      (t : TensorProduct k B B) :
      contractLaurent z
          (TensorProduct.map inclusion.toLinearMap inclusion.toLinearMap t) =
        inclusion (contractSource z t) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
        simp [contractLaurent, contractSource, coefficient]
  have exists_character_preimage_of_coefficient_ne_zero
      (q : B) (z : Fin n → ℤ) (hz : (inclusion q).coeff z ≠ 0) :
      ∃ r : B, inclusion r = AddMonoidAlgebra.single z 1 := by
    let c := (inclusion q).coeff z
    let r := contractSource z (comultiplication q)
    have hr : inclusion r = c • AddMonoidAlgebra.single z 1 := by
      rw [← contractLaurent_inclusionTensor]
      rw [← diagonalTensor_inclusion]
      exact contractLaurent_diagonalTensor z (inclusion q)
    refine ⟨c⁻¹ • r, ?_⟩
    rw [map_smul, hr, smul_smul]
    simp [c, hz]
  have pointCharacter_neg (z : Fin n → ℤ) (x : Variety.Point D) :
      pointCharacter (-z) x = (pointCharacter z x)⁻¹ := by
    change (↑(∏ i, (dPointEquiv n x i) ^ (-z) i) : k) =
      (↑(∏ i, (dPointEquiv n x i) ^ z i) : k)⁻¹
    rw [← Units.val_inv_eq_inv_val]
    apply congrArg Units.val
    simp [Finset.prod_inv_distrib]
  have pointCharacter_inv (z : Fin n → ℤ) (x : Variety.Point D) :
      pointCharacter z x⁻¹ = (pointCharacter z x)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← (pointCharacter z).map_mul,
      show x * x⁻¹ = 1 by exact mul_inv_cancel x]
    exact (pointCharacter z).map_one
  have exists_inverse_character_preimage
      (z : Fin n → ℤ) (q : B)
      (hq : inclusion q = AddMonoidAlgebra.single z 1) :
      ∃ r : B, inclusion r = AddMonoidAlgebra.single (-z) 1 := by
    let r := (AlgebraicGroup.invMorphism H).pullbackAlgHom q
    refine ⟨r, ?_⟩
    apply laurentEquiv.injective
    rw [inclusion_apply, laurentEquiv_single, one_smul]
    apply Variety.PolynomialFunction.ext
    intro x
    have hqA : pull q = character (Multiplicative.ofAdd z) := by
      rw [← inclusion_apply]
      rw [hq, laurentEquiv_single, one_smul]
    have hqx := congrArg (fun a : A => a (x⁻¹)) hqA
    change q ((f.onPoints x)⁻¹) = character (Multiplicative.ofAdd (-z)) x
    rw [← f.onPoints.map_inv]
    calc
      q (f.onPoints x⁻¹) = pull q x⁻¹ := rfl
      _ = character (Multiplicative.ofAdd z) x⁻¹ := hqx
      _ = pointCharacter z x⁻¹ := character_apply z x⁻¹
      _ = (pointCharacter z x)⁻¹ := pointCharacter_inv z x
      _ = pointCharacter (-z) x := (pointCharacter_neg z x).symm
      _ = character (Multiplicative.ofAdd (-z)) x :=
        (character_apply (-z) x).symm
  let coordinateFunction (i : H.Coordinates) : B :=
    Variety.PolynomialFunction.ofPolynomial H (MvPolynomial.X i)
  let support : Finset (Fin n → ℤ) :=
    Finset.univ.biUnion fun i : H.Coordinates =>
      (inclusion (coordinateFunction i)).coeff.support
  let m := support.card
  let enumerate : Fin m ≃ {z // z ∈ support} := support.equivFin.symm
  let exponent (r : Fin m) : Fin n → ℤ := (enumerate r).val
  have exponent_occurs (r : Fin m) :
      ∃ i : H.Coordinates,
        (inclusion (coordinateFunction i)).coeff (exponent r) ≠ 0 := by
    have hr : exponent r ∈ support := (enumerate r).property
    rw [show support = Finset.univ.biUnion fun i : H.Coordinates =>
        (inclusion (coordinateFunction i)).coeff.support by rfl,
      Finset.mem_biUnion] at hr
    obtain ⟨i, _hi, hir⟩ := hr
    exact ⟨i, Finsupp.mem_support_iff.mp hir⟩
  choose sourceIndex hsourceIndex using exponent_occurs
  have exists_positive (r : Fin m) :
      ∃ q : B, inclusion q = AddMonoidAlgebra.single (exponent r) 1 :=
    exists_character_preimage_of_coefficient_ne_zero
      (coordinateFunction (sourceIndex r)) (exponent r) (hsourceIndex r)
  choose positive hpositive using exists_positive
  have exists_negative (r : Fin m) :
      ∃ q : B, inclusion q = AddMonoidAlgebra.single (-(exponent r)) 1 :=
    exists_inverse_character_preimage (exponent r) (positive r) (hpositive r)
  choose negative hnegative using exists_negative
  have positive_mul_negative (r : Fin m) : positive r * negative r = 1 := by
    apply inclusion_injective
    calc
      inclusion (positive r * negative r) =
          inclusion (positive r) * inclusion (negative r) :=
        inclusion.map_mul _ _
      _ = 1 := by
        rw [hpositive, hnegative]
        simp [AddMonoidAlgebra.one_def]
      _ = inclusion 1 := inclusion.map_one.symm
  have negative_mul_positive (r : Fin m) : negative r * positive r = 1 := by
    rw [mul_comm]
    exact positive_mul_negative r
  let sourceUnit (r : Fin m) : Bˣ :=
    { val := positive r
      inv := negative r
      val_inv := positive_mul_negative r
      inv_val := negative_mul_positive r }
  have positive_pull (r : Fin m) :
      pull (positive r) = character (Multiplicative.ofAdd (exponent r)) := by
    rw [← inclusion_apply, hpositive, laurentEquiv_single, one_smul]
  have positive_mul (r : Fin m) (a b : Variety.Point H) :
      positive r (a * b) = positive r a * positive r b := by
    obtain ⟨x, rfl⟩ := hf a
    obtain ⟨y, rfl⟩ := hf b
    rw [← f.onPoints.map_mul]
    change pull (positive r) (x * y) =
      pull (positive r) x * pull (positive r) y
    rw [positive_pull]
    rw [character_apply, character_apply, character_apply,
      (pointCharacter (exponent r)).map_mul]
  have positive_one (r : Fin m) : positive r (1 : Variety.Point H) = 1 := by
    have hnonzero : positive r (1 : Variety.Point H) ≠ 0 := by
      intro hz
      have h := congrArg (fun q : B => q (1 : Variety.Point H))
        (positive_mul_negative r)
      rw [polynomialFunction_mul_apply, hz, zero_mul] at h
      exact zero_ne_one h
    apply mul_left_cancel₀ hnonzero
    rw [← positive_mul r, one_mul, mul_one]
  let evaluation (x : Variety.Point H) : B →+* k :=
    { toFun := fun q => q x
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let jPoint (x : Variety.Point H) : Variety.Point (dVariety k m) :=
    (dPointEquiv m).symm fun r =>
      (sourceUnit r).map (evaluation x).toMonoidHom
  let jVariety : Variety.Morphism H (dVariety k m) :=
    { toFun := jPoint
      regular := by
        intro c
        cases c with
        | inl i =>
            rcases (positive i.down).representedBy with ⟨p, hp⟩
            refine ⟨p, ?_⟩
            intro x
            rw [show jPoint x = (dPointEquiv m).symm (fun r =>
                (sourceUnit r).map (evaluation x).toMonoidHom) by rfl,
              dPointEquiv_symm_val_inl]
            change positive i.down x = evalPolynomial x.val p
            exact hp x
        | inr i =>
            rcases (negative i.down).representedBy with ⟨p, hp⟩
            refine ⟨p, ?_⟩
            intro x
            rw [show jPoint x = (dPointEquiv m).symm (fun r =>
                (sourceUnit r).map (evaluation x).toMonoidHom) by rfl,
              dPointEquiv_symm_val_inr]
            change negative i.down x = evalPolynomial x.val p
            exact hp x }
  let j : Morphism H (dVariety k m) :=
    { toVariety := jVariety
      map_one := by
        apply (dPointEquiv m).injective
        rw [dPointEquiv_one]
        change (fun r => (sourceUnit r).map
          (evaluation (1 : Variety.Point H)).toMonoidHom) = 1
        funext r
        apply Units.ext
        exact positive_one r
      map_mul := by
        intro x y
        apply (dPointEquiv m).injective
        rw [dPointEquiv_mul]
        change (fun r => (sourceUnit r).map
            (evaluation (x * y)).toMonoidHom) =
          (fun r => (sourceUnit r).map (evaluation x).toMonoidHom) *
            fun r => (sourceUnit r).map (evaluation y).toMonoidHom
        funext r
        apply Units.ext
        exact positive_mul r x y }
  have coordinate_support (i : H.Coordinates) (z : Fin n → ℤ)
      (hz : z ∈ (inclusion (coordinateFunction i)).coeff.support) :
      z ∈ support := by
    rw [show support = Finset.univ.biUnion fun i : H.Coordinates =>
        (inclusion (coordinateFunction i)).coeff.support by rfl,
      Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, hz⟩
  let supportIndex (z : Fin n → ℤ) (hz : z ∈ support) : Fin m :=
    enumerate.symm ⟨z, hz⟩
  have exponent_supportIndex (z : Fin n → ℤ) (hz : z ∈ support) :
      exponent (supportIndex z hz) = z := by
    change (enumerate (enumerate.symm ⟨z, hz⟩)).val = z
    exact congrArg Subtype.val (enumerate.apply_symm_apply ⟨z, hz⟩)
  let targetCoordinate (r : Fin m) :
      Variety.PolynomialFunction (dVariety k m) :=
    Variety.PolynomialFunction.ofPolynomial (dVariety k m)
      (MvPolynomial.X (Sum.inl (ULift.up r)))
  have pull_targetCoordinate (r : Fin m) :
      j.toVariety.pullbackAlgHom (targetCoordinate r) = positive r := by
    apply Variety.PolynomialFunction.ext
    intro x
    change targetCoordinate r (j.toVariety.toFun x) = positive r x
    change evalPolynomial (j.toVariety.toFun x).val
      (MvPolynomial.X (Sum.inl (ULift.up r))) = positive r x
    rw [evalPolynomial_X]
    change (jPoint x).val (Sum.inl (ULift.up r)) = positive r x
    rw [show jPoint x = (dPointEquiv m).symm (fun s =>
        (sourceUnit s).map (evaluation x).toMonoidHom) by rfl,
      dPointEquiv_symm_val_inl]
    rfl
  let coordinateLift (i : H.Coordinates) :
      Variety.PolynomialFunction (dVariety k m) :=
    ∑ z ∈ (inclusion (coordinateFunction i)).coeff.support.attach,
      (inclusion (coordinateFunction i)).coeff z.val •
        targetCoordinate
          (supportIndex z.val (coordinate_support i z.val z.property))
  have laurent_expansion (q : AddMonoidAlgebra k (Fin n → ℤ)) :
      (∑ z ∈ q.coeff.support.attach,
          q.coeff z.val • AddMonoidAlgebra.single z.val 1) = q := by
    rw [q.coeff.support.sum_attach (fun z =>
      q.coeff z • AddMonoidAlgebra.single z 1)]
    exact (AddMonoidAlgebra.lift_unique
      (AlgHom.id k (AddMonoidAlgebra k (Fin n → ℤ))) q).symm
  have pull_coordinateLift (i : H.Coordinates) :
      j.toVariety.pullbackAlgHom (coordinateLift i) = coordinateFunction i := by
    apply inclusion_injective
    rw [show coordinateLift i =
        ∑ z ∈ (inclusion (coordinateFunction i)).coeff.support.attach,
          (inclusion (coordinateFunction i)).coeff z.val •
            targetCoordinate
              (supportIndex z.val (coordinate_support i z.val z.property)) by rfl]
    simp only [map_sum, map_smul, pull_targetCoordinate, hpositive,
      exponent_supportIndex]
    exact laurent_expansion (inclusion (coordinateFunction i))
  refine ⟨m, j, ?_⟩
  intro q
  rcases q.representedBy with ⟨p, hp⟩
  let lift : Variety.PolynomialFunction (dVariety k m) :=
    MvPolynomial.aeval coordinateLift p
  refine ⟨lift, ?_⟩
  have hcoordinate :
      j.toVariety.pullbackAlgHom.comp (MvPolynomial.aeval coordinateLift) =
        evaluationAlgHom H := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X,
      pull_coordinateLift]
    rfl
  change j.toVariety.pullbackAlgHom lift = q
  rw [show j.toVariety.pullbackAlgHom lift = evaluationAlgHom H p by
    exact DFunLike.congr_fun hcoordinate p]
  apply Variety.PolynomialFunction.ext
  intro x
  exact (hp x).symm

end Theory.AlgebraicGroup
