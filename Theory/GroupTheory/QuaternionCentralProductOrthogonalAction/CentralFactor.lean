module
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Geometry

/-!
# Square action with an elementary central direct factor

For `E ≃ P × D`, where P is a quaternion central product and D is elementary
abelian of exponent two, projection identifies E/Z(E) with P/Z(P). The old
square form has value zero exactly on representatives squaring to one. This
characterization is invariant under every automorphism of E, including those
which do not preserve the chosen P factor. It gives the actual quotient action
in O₄⁺(2), with the same kernel as the intrinsic central-quotient action.

Source: Aschbacher--Smith, 2.4.29, printed p.545, the action on P T_C/Z(P T_C).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup.QuaternionCentralProductData
variable {P D E : Type*} [Group P] [Group D] [IsElementaryAbelian 2 D]
  [Group E] (e : E ≃* P × D)

noncomputable def centralFactorProjection : E →* P ⧸ center P :=
  (QuotientGroup.mk' (center P)).comp ((MonoidHom.fst P D).comp e.toMonoidHom)

omit [IsElementaryAbelian 2 D] in
theorem centralFactorProjection_surjective : Function.Surjective (centralFactorProjection e) := by
  intro q
  obtain ⟨p,rfl⟩ := QuotientGroup.mk'_surjective (center P) q
  exact ⟨e.symm (p,1),by simp [centralFactorProjection]⟩

theorem centralFactorProjection_ker : (centralFactorProjection e).ker = center E := by
  ext x
  change QuotientGroup.mk' (center P) (e x).1 = 1 ↔ x ∈ center E
  change ((e x).1 : P ⧸ center P) = 1 ↔ x ∈ center E
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hx
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simp only [map_mul]
    apply Prod.ext
    · exact mem_center_iff.mp hx (e y).1
    · change (e y).2 * (e x).2 = (e x).2 * (e y).2
      exact mul_comm _ _
  · intro hx
    apply mem_center_iff.mpr
    intro p
    have hh := congrArg (fun x => (e x).1) (mem_center_iff.mp hx (e.symm (p,1)))
    simpa only [map_mul,e.apply_symm_apply,Prod.fst_mul] using hh

noncomputable def centralFactorQuotientEquiv : E ⧸ center E ≃* P ⧸ center P :=
  (QuotientGroup.quotientMulEquivOfEq (centralFactorProjection_ker e).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (centralFactorProjection e)
      (centralFactorProjection_surjective e))

@[simp] theorem centralFactorQuotientEquiv_mk (x : E) :
    centralFactorQuotientEquiv e (QuotientGroup.mk' (center E) x) =
      QuotientGroup.mk' (center P) (e x).1 := rfl

variable [Finite P] (d : QuaternionCentralProductData P)

theorem centralFactor_square_zero_iff (x : E) :
    d.quadraticForm (Additive.ofMul (centralFactorProjection e x)) = 0 ↔ x ^ 2 = 1 := by
  change d.quadraticForm (Additive.ofMul (QuotientGroup.mk' (center P) (e x).1)) = 0 ↔ x ^ 2 = 1
  rw [d.quadraticForm_apply,d.binarySquare_mk,d.centerCoordinate_eq_zero_iff]
  rw [Subtype.ext_iff]
  change (e x).1 ^ 2 = 1 ↔ x ^ 2 = 1
  rw [← e.injective.eq_iff, map_pow, map_one]
  have hD : (e x).2 ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 D) _
  change (e x).1 ^ 2 = 1 ↔ ((e x).1 ^ 2, (e x).2 ^ 2) = (1,1)
  simp only [Prod.mk.injEq,hD,and_true]

noncomputable def centralFactorQuotientAction : MulAut E →* MulAut (P ⧸ center P) :=
  (MulAut.congr (centralFactorQuotientEquiv e)).toMonoidHom.comp (quotientAut (center E))

omit [Finite P] in
@[simp] theorem centralFactorQuotientAction_mk (a : MulAut E) (x : E) :
    centralFactorQuotientAction e a (centralFactorProjection e x) =
      centralFactorProjection e (a x) := by
  change centralFactorQuotientEquiv e (quotientAut (center E) a
    ((centralFactorQuotientEquiv e).symm (centralFactorQuotientEquiv e
      (QuotientGroup.mk' (center E) x)))) = _
  rw [MulEquiv.symm_apply_apply,quotientAut_apply_mk,centralFactorQuotientEquiv_mk]
  rfl

theorem centralFactor_quadraticForm_invariant (a : MulAut E) (v : P ⧸ center P) :
    d.quadraticForm (Additive.ofMul (centralFactorQuotientAction e a v)) =
      d.quadraticForm (Additive.ofMul v) := by
  obtain ⟨x,rfl⟩ := centralFactorProjection_surjective e v
  rw [centralFactorQuotientAction_mk]
  apply (by decide : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b)
  rw [d.centralFactor_square_zero_iff e,d.centralFactor_square_zero_iff e,
    ← map_pow, map_eq_one_iff _ a.injective]

noncomputable def centralFactorLinearAction : MulAut E →*
    (d.SquareSpace ≃ₗ[ZMod 2] d.SquareSpace) where
  toFun a := {
    toFun v := Additive.ofMul (centralFactorQuotientAction e a v.toMul)
    invFun v := Additive.ofMul ((centralFactorQuotientAction e a).symm v.toMul)
    left_inv v := (centralFactorQuotientAction e a).symm_apply_apply v.toMul
    right_inv v := (centralFactorQuotientAction e a).apply_symm_apply v.toMul
    map_add' v w := congrArg Additive.ofMul (map_mul (centralFactorQuotientAction e a) v.toMul w.toMul)
    map_smul' r v := by
      have binary : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
      rcases binary r with rfl | rfl
      · simp only [RingHom.id_apply,zero_smul]
        exact congrArg Additive.ofMul (map_one (centralFactorQuotientAction e a))
      · simp only [one_smul,RingHom.id_apply] }
  map_one' := by
    ext v
    exact congrArg (fun a : MulAut (P ⧸ center P) => Additive.ofMul (a v.toMul))
      (map_one (centralFactorQuotientAction e))
  map_mul' a b := by
    ext v
    exact congrArg (fun a : MulAut (P ⧸ center P) => Additive.ofMul (a v.toMul))
      (map_mul (centralFactorQuotientAction e) a b)

noncomputable def centralFactorIsometryAction : MulAut E →* d.squareIsometries :=
  (d.centralFactorLinearAction e).codRestrict d.squareIsometries
    (fun a => (d.mem_squareIsometries _).mpr
      (fun v => d.centralFactor_quadraticForm_invariant e a v.toMul))

noncomputable def centralFactorWreathAction : MulAut E →* BinaryFourPlus.Wreath :=
  d.squareIsometriesEquivWreath.toMonoidHom.comp (d.centralFactorIsometryAction e)

omit [Finite P] in
@[simp] theorem centralFactorQuotientAction_equiv (a : MulAut E) (v : E ⧸ center E) :
    centralFactorQuotientAction e a (centralFactorQuotientEquiv e v) =
      centralFactorQuotientEquiv e (quotientAut (center E) a v) := by
  change centralFactorQuotientEquiv e (quotientAut (center E) a
    ((centralFactorQuotientEquiv e).symm (centralFactorQuotientEquiv e v))) = _
  rw [MulEquiv.symm_apply_apply]

/-- The actual quotient action, in the marked binary plus coordinates. -/
theorem centralFactorWreathAction_apply (a : MulAut E) (v : E ⧸ center E)
    (i : BinaryFourPlus.C2) :
    BinaryFourPlus.coordinate (d.squareCoordinates (Additive.ofMul
      (centralFactorQuotientEquiv e (quotientAut (center E) a v)))) i =
      BinaryFourPlus.planeLinear ((d.centralFactorWreathAction e a).left i)
        (BinaryFourPlus.coordinate (d.squareCoordinates (Additive.ofMul
          (centralFactorQuotientEquiv e v)))
          ((d.centralFactorWreathAction e a).right⁻¹*i)) := by
  have h := d.squareIsometriesEquivWreath_action (d.centralFactorIsometryAction e a)
    (Additive.ofMul (centralFactorQuotientEquiv e v)) i
  change BinaryFourPlus.coordinate (d.squareCoordinates (Additive.ofMul
    (centralFactorQuotientAction e a (centralFactorQuotientEquiv e v)))) i = _ at h
  rwa [centralFactorQuotientAction_equiv] at h

/-- The orthogonal representation kills exactly the actual central-quotient kernel. -/
theorem centralFactorWreathAction_ker :
    (d.centralFactorWreathAction e).ker = (quotientAut (center E)).ker := by
  ext a
  change d.centralFactorWreathAction e a = 1 ↔ quotientAut (center E) a = 1
  have he : d.centralFactorWreathAction e a = 1 ↔ centralFactorQuotientAction e a = 1 := by
    constructor
    · intro ha
      have hi : d.centralFactorIsometryAction e a = 1 :=
        d.squareIsometriesEquivWreath.injective (ha.trans d.squareIsometriesEquivWreath.map_one.symm)
      apply MulEquiv.ext
      intro v
      exact congrArg (fun b : d.squareIsometries => (b.val (Additive.ofMul v)).toMul) hi
    · intro ha
      have hi : d.centralFactorIsometryAction e a = 1 := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        exact congrArg (fun b : MulAut (P ⧸ center P) => Additive.ofMul (b v.toMul)) ha
      change d.squareIsometriesEquivWreath (d.centralFactorIsometryAction e a) = 1
      rw [hi,map_one]
  rw [he]
  exact (MulAut.congr (centralFactorQuotientEquiv e)).map_eq_one_iff

end Subgroup.QuaternionCentralProductData
