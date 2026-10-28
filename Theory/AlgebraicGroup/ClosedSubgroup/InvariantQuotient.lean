module

public import Theory.AlgebraicGroup.ClosedSubgroup.InvariantCoordinates
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.Invariant
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.Presentation

namespace Theory.AlgebraicGroup

open scoped TensorProduct

universe u

set_option linter.style.haveILetI false

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A normal closed subgroup has an algebraic quotient whenever its ring of
right-invariant coordinates is of finite type. -/
public theorem ClosedSubgroup.quotient_exists_of_finiteType_rightInvariantCoordinateRing
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal)
    [Algebra.FiniteType k (AlgebraicGroup.rightInvariantCoordinateRing H)] :
    ∃ (Q : Variety k) (_ : AlgebraicGroup Q)
      (π : AlgebraicGroup.Morphism G Q),
      Function.Surjective π.onPoints ∧ π.kernel = H.toSubgroup ∧
        ∀ {I : Variety k} [AlgebraicGroup I]
          (φ : AlgebraicGroup.Morphism G I), H.toSubgroup ≤ φ.kernel →
            ∃! ψ : AlgebraicGroup.Morphism Q I, ψ.comp π = φ := by
  classical
  let B := AlgebraicGroup.rightInvariantCoordinateRing H
  letI : HopfAlgebra k B :=
    rightInvariantCoordinateHopfAlgebra H hN
  let : IsReduced B := rightInvariantCoordinateRing_isReduced H
  let P : ReducedFiniteTypeAlgebraPresentation k B :=
    Classical.choice (ReducedFiniteTypeAlgebraPresentation.exists k B)
  let Q := P.toVariety
  letI : AlgebraicGroup Q := by
    dsimp only [Q]
    exact P.algebraicGroup
  let evalInvariant (g : Variety.Point G) : B →ₐ[k] k :=
    (Variety.PolynomialFunction.evalAlgHom G g).comp B.val
  have evalInvariant_one (f : B) :
      evalInvariant 1 f = AlgebraicGroup.rightInvariantCoordinateCounit H f := by
    exact (AlgebraicGroup.rightInvariantCoordinateCounit_apply H f).symm
  have evalInvariant_mul (g x : Variety.Point G) (f : B) :
      evalInvariant (g * x) f =
        (WithConv.toConv (evalInvariant g) *
          WithConv.toConv (evalInvariant x)).ofConv f := by
    have ht (t : B ⊗[k] B) :
        polynomialFunctionTensor G G
            (TensorProduct.map B.val.toLinearMap B.val.toLinearMap t)
              ((Variety.prodPointEquiv G G).symm (g, x)) =
          Algebra.TensorProduct.lift
            (evalInvariant g) (evalInvariant x)
              (fun _ _ => Commute.all _ _) t := by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb =>
          simp only [map_add, Variety.PolynomialFunction.toFun,
            Subring.coe_add, Pi.add_apply]
          exact congrArg₂ (fun a b => a + b) ha hb
      | tmul a b =>
          rw [TensorProduct.map_tmul, polynomialFunctionTensor_tmul,
            Algebra.TensorProduct.lift_tmul]
          rfl
    rw [AlgHom.convMul_apply]
    change f.val (g * x) = _
    rw [← AlgebraicGroup.coordinateComultiplication_apply G f.val g x]
    rw [← AlgebraicGroup.rightInvariantCoordinateComultiplication_apply H hN f]
    exact ht (AlgebraicGroup.rightInvariantCoordinateComultiplication H hN f)
  let pointMap : Variety.Point G →* Variety.Point Q :=
    { toFun := fun g => P.pointCharacterEquiv.symm
        (WithConv.toConv (evalInvariant g))
      map_one' := by
        change P.pointCharacterEquiv.symm
            (WithConv.toConv (evalInvariant 1)) =
          P.pointCharacterEquiv.symm 1
        apply P.pointCharacterEquiv.injective
        rw [P.pointCharacterEquiv.apply_symm_apply,
          P.pointCharacterEquiv.apply_symm_apply]
        apply WithConv.ofConv_injective
        apply AlgHom.ext
        intro f
        exact evalInvariant_one f
      map_mul' := by
        intro g x
        change P.pointCharacterEquiv.symm
            (WithConv.toConv (evalInvariant (g * x))) =
          @Mul.mul (Variety.Point P.toVariety) P.pointGroup.toMul
            (P.pointCharacterEquiv.symm (WithConv.toConv (evalInvariant g)))
            (P.pointCharacterEquiv.symm (WithConv.toConv (evalInvariant x)))
        apply P.pointCharacterEquiv.injective
        rw [P.pointCharacterEquiv_mul]
        simp only [Equiv.apply_symm_apply]
        apply WithConv.ofConv_injective
        apply AlgHom.ext
        intro f
        exact evalInvariant_mul g x f }
  let α : Variety.PolynomialFunction Q →ₐ[k] Variety.PolynomialFunction G :=
    B.val.comp P.polynomialFunctionAlgEquiv.symm.toAlgHom
  have hα (a : Variety.PolynomialFunction Q) (g : Variety.Point G) :
      α a g = a (pointMap g) := by
    change (P.polynomialFunctionAlgEquiv.symm a).val g = a (pointMap g)
    change evalInvariant g (P.polynomialFunctionAlgEquiv.symm a) = _
    have hchar := congrArg
      (fun φ : WithConv (B →ₐ[k] k) =>
        φ.ofConv (P.polynomialFunctionAlgEquiv.symm a))
      (P.pointCharacterEquiv.apply_symm_apply
        (WithConv.toConv (evalInvariant g)))
    calc
      evalInvariant g (P.polynomialFunctionAlgEquiv.symm a) =
          (P.pointCharacterEquiv
            (P.pointCharacterEquiv.symm
              (WithConv.toConv (evalInvariant g)))).ofConv
            (P.polynomialFunctionAlgEquiv.symm a) := hchar.symm
      _ = a (pointMap g) := by
        change (P.polynomialFunctionAlgEquiv
          (P.polynomialFunctionAlgEquiv.symm a)) (pointMap g) = _
        rw [P.polynomialFunctionAlgEquiv.apply_symm_apply]
  obtain ⟨π, hπpoint⟩ :=
    Morphism.exists_of_pointHom_of_polynomialFunctionAlgHom pointMap α hα
  have hπpull : π.toVariety.pullbackAlgHom = α := by
    apply AlgHom.ext
    intro a
    apply Variety.PolynomialFunction.ext
    intro g
    change a (π.onPoints g) = α a g
    rw [hπpoint]
    exact (hα a g).symm
  have hαinj : Function.Injective α := by
    intro a b hab
    apply P.polynomialFunctionAlgEquiv.symm.injective
    apply Subtype.ext
    exact hab
  have hπsurj : Function.Surjective π.onPoints := by
    have himage : IsZariskiClosed Q (Set.range π.onPoints) := by
      rw [← π.image_carrier]
      exact π.image_isZariskiClosed
    by_contra hnot
    change ¬ ∀ y, ∃ g, π.onPoints g = y at hnot
    obtain ⟨y, hyrange⟩ := not_forall.mp hnot
    change y ∉ Set.range π.onPoints at hyrange
    have hyclosed : ¬ ∀ p ∈ Variety.closedEquations himage,
        evalPolynomial y.val p = 0 := by
      intro hy
      apply hyrange
      rw [Variety.closedEquations_spec himage]
      exact hy
    obtain ⟨p, hp⟩ := not_forall.mp hyclosed
    obtain ⟨hp, hpne⟩ := Classical.not_imp.mp hp
    let a := Variety.PolynomialFunction.ofPolynomial Q p
    have hzero : α a = 0 := by
      apply Variety.PolynomialFunction.ext
      intro g
      rw [← hπpull]
      change a (π.onPoints g) = 0
      have hg : π.onPoints g ∈ Set.range π.onPoints := ⟨g, rfl⟩
      rw [Variety.closedEquations_spec himage] at hg
      exact hg p hp
    have azero : a = 0 := hαinj (by simpa using hzero)
    have := congrArg (fun f : Variety.PolynomialFunction Q => f y) azero
    exact hpne (by simpa [a, Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun] using this)
  have hπker : π.kernel = H.toSubgroup := by
    ext g
    change π.onPoints g = 1 ↔ g ∈ H.toSubgroup
    rw [hπpoint]
    constructor
    · intro hg
      have hpoint : pointMap g = pointMap 1 := hg.trans pointMap.map_one.symm
      have hchar := congrArg P.pointCharacterEquiv hpoint
      have heval : evalInvariant g = evalInvariant 1 := by
        apply WithConv.toConv_injective
        calc
          WithConv.toConv (evalInvariant g) =
              P.pointCharacterEquiv
                (P.pointCharacterEquiv.symm
                  (WithConv.toConv (evalInvariant g))) :=
            (P.pointCharacterEquiv.apply_symm_apply _).symm
          _ = P.pointCharacterEquiv (pointMap g) := rfl
          _ = P.pointCharacterEquiv (pointMap 1) := hchar
          _ = P.pointCharacterEquiv
              (P.pointCharacterEquiv.symm
                (WithConv.toConv (evalInvariant 1))) := rfl
          _ = WithConv.toConv (evalInvariant 1) :=
            P.pointCharacterEquiv.apply_symm_apply _
      obtain ⟨m, c, hc⟩ :=
        H.finiteRightInvariantCoordinates_eq_iff_inv_mul_mem hN
      have hcoords : ∀ i j, (c i j).val 1 = (c i j).val g := by
        intro i j
        exact congrArg (fun φ : B →ₐ[k] k => φ (c i j)) heval |>.symm
      simpa only [inv_one, one_mul] using (hc 1 g).mp hcoords
    · intro hg
      rw [← pointMap.map_one]
      apply P.pointCharacterEquiv.injective
      change P.pointCharacterEquiv
          (P.pointCharacterEquiv.symm
            (WithConv.toConv (evalInvariant g))) =
        P.pointCharacterEquiv
          (P.pointCharacterEquiv.symm
            (WithConv.toConv (evalInvariant 1)))
      rw [P.pointCharacterEquiv.apply_symm_apply,
        P.pointCharacterEquiv.apply_symm_apply]
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro f
      change f.val g = f.val 1
      have hinv :=
        (AlgebraicGroup.mem_rightInvariantCoordinateRing_iff H f.val).mp
          f.property 1 g hg
      simpa using hinv
  refine ⟨Q, inferInstance, π, hπsurj, hπker, ?_⟩
  intro I _ φ hφ
  obtain ⟨ψ, hψ, hψuniq⟩ :=
    π.pointLift_existsUnique_of_surjective_kernel
      H hN hπsurj hπker φ hφ
  let γ := φ.pullbackToRightInvariantCoordinateRing H hφ
  let β : Variety.PolynomialFunction I →ₐ[k]
      Variety.PolynomialFunction Q :=
    P.polynomialFunctionAlgEquiv.toAlgHom.comp γ
  have hβ (a : Variety.PolynomialFunction I) (y : Variety.Point Q) :
      β a y = a (ψ y) := by
    obtain ⟨g, rfl⟩ := hπsurj y
    have hψg := congrArg
      (fun θ : Variety.Point G →* Variety.Point I => θ g) hψ
    calc
      β a (π.onPoints g) = β a (pointMap g) := by rw [← hπpoint]
      _ = α (β a) g := (hα (β a) g).symm
      _ = a (φ.onPoints g) := by
        change (P.polynomialFunctionAlgEquiv.symm
          (P.polynomialFunctionAlgEquiv (γ a))).val g = _
        rw [P.polynomialFunctionAlgEquiv.symm_apply_apply]
        rfl
      _ = a (ψ (π.onPoints g)) := congrArg (fun x => a x) hψg.symm
  obtain ⟨Ψ, hΨpoints⟩ :=
    Morphism.exists_of_pointHom_of_polynomialFunctionAlgHom ψ β hβ
  have hΨcomp : Ψ.comp π = φ := by
    apply Morphism.ext
    funext g
    change Ψ.onPoints (π.onPoints g) = φ.onPoints g
    rw [hΨpoints]
    exact congrArg (fun θ : Variety.Point G →* Variety.Point I => θ g) hψ
  refine ⟨Ψ, hΨcomp, ?_⟩
  intro Ψ' hΨ'comp
  have hΨ'points : Ψ'.onPoints.comp π.onPoints = φ.onPoints := by
    apply MonoidHom.ext
    intro g
    exact congrArg
      (fun θ : AlgebraicGroup.Morphism G I => θ.onPoints g) hΨ'comp
  have hΨ'unique := hψuniq Ψ'.onPoints hΨ'points
  apply Morphism.ext
  funext y
  change Ψ'.onPoints y = Ψ.onPoints y
  rw [hΨ'unique, hΨpoints]

end Theory.AlgebraicGroup
