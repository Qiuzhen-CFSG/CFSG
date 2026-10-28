module
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.StandardComplement
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.BinarySixObstruction.Basic
public import Theory.LinearAlgebra.QuadraticForm.BinaryAnisotropic
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Actual coordinates for binary quadratic six-spaces

Split two hyperbolic planes using nonsingularity and the binary anisotropic
dimension bound. The remaining plane is either hyperbolic or anisotropic,
as checked by a two-dimensional change of basis. Explicit regrouping of the
coordinates gives isometries to the literal plus and minus models.

The final theorem supports arbitrary universe levels. These are isometries
of quadratic forms, retaining the quadratic values and their natural actions.
Source: the low-dimensional orthogonal alternatives in Aschbacher--Smith
G.10.15, printed p.363; the hyperbolic splitting construction in the imported,
ATLAS-attributed quadratic-space modules.
-/

public noncomputable section
open Module ClassicalOrthogonal.Quadratic
open ClassicalOrthogonal.Minus
namespace QuadraticForm.BinarySixCoordinates
abbrev F := ZMod 2
abbrev Plane := F × F
abbrev H := hyperbolic F
abbrev A := plane F 1

private theorem complement_nd {V : Type} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)
    (e f : V) (he : Q e=0) (hf : Q f=0) (hef : Q.polarBilin e f=1) :
    (complementForm Q e f).polarBilin.Nondegenerate := by
  have hinj : (complementForm Q e f).polarBilin.SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    apply hQ.1 x.val
    intro y
    have hh := hx (split Q e f he hf hef y).2
    rw [complementForm_polar] at hh
    have hy := (split Q e f he hf hef).symm_apply_apply y
    change Q.polarBilin y f • e+Q.polarBilin y e • f+
      ((split Q e f he hf hef y).2 : V)=y at hy
    have hxe : Q.polarBilin x.val e=0 := x.property.1
    have hxf : Q.polarBilin x.val f=0 := x.property.2
    rw [← hy,map_add,map_add,map_smul,map_smul,hxe,hxf,
      smul_zero,smul_zero,zero_add,zero_add,hh]
  exact ⟨hinj,fun x hx => hinj x (fun y => (polar_swap _ x y).trans (hx y))⟩

private theorem hyperbolic_pair {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) (hd : 2 < finrank F V) :
    ∃ e f : V,Q e=0 ∧ Q f=0 ∧ Q.polarBilin e f=1 := by
  let : Finite V := Module.finite_of_finite F
  have hna : ¬ Q.Anisotropic := by
    intro han
    have hh := Q.finrank_le_twice_of_anisotropic_binary han
    simp only [Module.finrank_self,mul_one] at hh
    change finrank F V ≤ 2 at hh
    omega
  obtain ⟨e,he,he0⟩ : ∃ e : V,Q e=0 ∧ e≠0 := by
    have hh : ¬∀ e : V,Q e=0 → e=0 := hna
    push Not at hh
    exact hh
  obtain ⟨f,hf⟩ := exists_normalized_partner Q e (fun hz => he0 (hQ.1 e hz))
  exact ⟨e,f-Q f • e,he,(partner_correction Q e f he hf).1,
    (partner_correction Q e f he hf).2⟩

private def splitIsometry {V : Type} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (e f : V) (he : Q e=0) (hf : Q f=0)
    (hef : Q.polarBilin e f=1) : Q.IsometryEquiv (H.prod (complementForm Q e f)) where
  toLinearEquiv := split Q e f he hf hef
  map_app' x := (form_split Q e f he hf hef x).symm

private def planeShear (a b : F) : Plane ≃ₗ[F] Plane where
  toFun z := if a=0 then (z.1+b*z.2,z.2) else (z.1,z.2+z.1)
  invFun z := if a=0 then (z.1+b*z.2,z.2) else (z.1,z.2+z.1)
  left_inv := by revert a b; decide
  right_inv := by revert a b; decide
  map_add' := by revert a b; decide
  map_smul' := by revert a b; decide

private theorem planeShear_form (a b : F) (hab : ¬(a=1 ∧ b=1)) (z : Plane) :
    H (planeShear a b z)=a*z.1^2+z.1*z.2+b*z.2^2 := by
  change (if a=0 then (z.1+b*z.2,z.2) else (z.1,z.2+z.1)).1 *
    (if a=0 then (z.1+b*z.2,z.2) else (z.1,z.2+z.1)).2 = _
  revert a b z
  decide

private theorem plane_classification {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) (hd : finrank F V=2) :
    Nonempty (Q.IsometryEquiv H) ∨ Nonempty (Q.IsometryEquiv A) := by
  let b := finBasisOfFinrankEq F V hd
  let c : V ≃ₗ[F] Plane := b.equivFun.trans (LinearEquiv.finTwoArrow F F)
  have hc (x : V) : x=(c x).1 • b 0+(c x).2 • b 1 := by
    simpa only [c,LinearEquiv.trans_apply,LinearEquiv.finTwoArrow_apply,
      Fin.sum_univ_two] using (b.sum_equivFun x).symm
  have hp : Q.polarBilin (b 0) (b 1)=1 := by
    apply (show ∀ a : F,a=0 ∨ a=1 from by decide) _ |>.resolve_left
    intro hz
    have hb0 : b 0=0 := hQ.1 _ (fun x => by
      rw [hc x,map_add,map_smul,map_smul,hz,polar_self]
      simp only [show (2 : F)=0 from by decide,zero_mul,smul_zero,zero_add])
    exact b.ne_zero 0 hb0
  have hform (x : V) : Q x=Q (b 0)*(c x).1^2+(c x).1*(c x).2+Q (b 1)*(c x).2^2 := by
    conv_lhs => rw [hc x]
    rw [QuadraticMap.map_add Q,Q.map_smul,Q.map_smul]
    change _+_+Q.polarBilin ((c x).1 • b 0) ((c x).2 • b 1)=_
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,hp,mul_one]
    ring
  by_cases ha : Q (b 0)=1 ∧ Q (b 1)=1
  · right
    refine ⟨{ toLinearEquiv := c, map_app' := ?_ }⟩
    intro x
    rw [hform,ha.1,ha.2]
    change plane F 1 (c x)=_
    rw [plane_apply]
    simp only [one_mul, CharTwo.sub_eq_add]
  · left
    refine ⟨{ toLinearEquiv := c.trans (planeShear (Q (b 0)) (Q (b 1))), map_app' := ?_ }⟩
    intro x
    change H (planeShear (Q (b 0)) (Q (b 1)) (c x)) = Q x
    exact (planeShear_form _ _ ha _).trans (hform x).symm

private def plusCoordinates : (Plane × (Plane × Plane)) ≃ₗ[F] ClassicalOrthogonal.VectorD 3 F where
  toFun z := Sum.elim ![z.1.1,z.2.1.1,z.2.2.1] ![z.1.2,z.2.1.2,z.2.2.2]
  invFun w := ((w (.inl 0),w (.inr 0)),((w (.inl 1),w (.inr 1)),(w (.inl 2),w (.inr 2))))
  left_inv z := rfl
  right_inv w := by
    funext i
    rcases i with i|i <;> fin_cases i <;> rfl
  map_add' z w := by
    funext i
    rcases i with i|i <;> fin_cases i <;> rfl
  map_smul' c z := by
    funext i
    rcases i with i|i <;> fin_cases i <;> rfl

private def plusIsometry : (H.prod (H.prod H)).IsometryEquiv (ClassicalOrthogonal.formD 3 F) where
  toLinearEquiv := plusCoordinates
  map_app' z := by
    simp only [ClassicalOrthogonal.formD_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,
      QuadraticMap.prod_apply,hyperbolic_apply]
    change z.1.1*z.1.2+(z.2.1.1*z.2.1.2+(z.2.2.1*z.2.2.2+0))=
      z.1.1*z.1.2+(z.2.1.1*z.2.1.2+z.2.2.1*z.2.2.2)
    rw [add_zero]

private def minusCoordinates : (Plane × (Plane × Plane)) ≃ₗ[F] Space F 2 where
  toFun z := (![z.1,z.2.1],z.2.2)
  invFun w := (w.1 0,(w.1 1,w.2))
  left_inv z := rfl
  right_inv w := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl
  map_add' z w := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl
  map_smul' c z := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl

private def minusIsometry : (H.prod (H.prod A)).IsometryEquiv (quadraticForm F 3) where
  toLinearEquiv := minusCoordinates
  map_app' z := by
    change BinarySixObstruction.naturalForm (minusCoordinates z) = _
    rw [BinarySixObstruction.naturalForm_eq]
    simp only [form_apply,Fin.sum_univ_two,QuadraticMap.prod_apply,hyperbolic_apply]
    change (z.1.1*z.1.2+z.2.1.1*z.2.1.2)+plane F 1 z.2.2=
      z.1.1*z.1.2+(z.2.1.1*z.2.1.2+plane F 1 z.2.2)
    exact add_assoc _ _ _

/-- Splitting two actual hyperbolic planes leaves a binary plane of either type. -/
theorem classify_coordinate {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) (hd : finrank F V=6) :
    Nonempty (Q.IsometryEquiv (ClassicalOrthogonal.formD 3 F)) ∨
      Nonempty (Q.IsometryEquiv (quadraticForm F 3)) := by
  obtain ⟨e,f,he,hf,hef⟩ := hyperbolic_pair Q hQ (by omega)
  let C := complementForm Q e f
  have hC := complement_nd Q hQ e f he hf hef
  have hdC : finrank F (complement Q e f)=4 := by
    have := finrank_complement Q e f he hf hef
    omega
  obtain ⟨a,b,ha,hb,hab⟩ := hyperbolic_pair C hC (by omega)
  have hdD : finrank F (complement C a b)=2 := by
    have := finrank_complement C a b ha hb hab
    omega
  let e0 := splitIsometry Q e f he hf hef
  let e1 := splitIsometry C a b ha hb hab
  rcases plane_classification (complementForm C a b) (complement_nd C hC a b ha hb hab) hdD with hp|hm
  · obtain ⟨j⟩ := hp
    exact Or.inl ⟨(e0.trans ((QuadraticMap.IsometryEquiv.refl H).prod
      (e1.trans ((QuadraticMap.IsometryEquiv.refl H).prod j)))).trans plusIsometry⟩
  · obtain ⟨j⟩ := hm
    exact Or.inr ⟨(e0.trans ((QuadraticMap.IsometryEquiv.refl H).prod
      (e1.trans ((QuadraticMap.IsometryEquiv.refl H).prod j)))).trans minusIsometry⟩

/-- The actual isometries are independent of the universe of the source space. -/
theorem classify {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) (hd : finrank F V=6) :
    Nonempty (Q.IsometryEquiv (ClassicalOrthogonal.formD 3 F)) ∨
      Nonempty (Q.IsometryEquiv (quadraticForm F 3)) := by
  let W := Fin 6 → F
  let e : W ≃ₗ[F] V := (finBasisOfFinrankEq F V hd).equivFun.symm
  let P := Q.comp e.toLinearMap
  let j : P.IsometryEquiv Q := { toLinearEquiv := e, map_app' := fun _ => rfl }
  have hp (x y : W) : P.polarBilin x y = Q.polarBilin (e x) (e y) := by
    simp only [P,QuadraticMap.polarBilin_comp,LinearMap.compl₁₂_apply,LinearEquiv.coe_coe]
  have hn : P.polarBilin.Nondegenerate := by
    constructor
    · intro x hx
      apply e.injective
      rw [map_zero]
      apply hQ.1
      intro y
      obtain ⟨y,rfl⟩ := e.surjective y
      exact (hp x y).symm.trans (hx y)
    · intro x hx
      apply e.injective
      rw [map_zero]
      apply hQ.2
      intro y
      obtain ⟨y,rfl⟩ := e.surjective y
      exact (hp y x).symm.trans (hx y)
  rcases classify_coordinate P hn (by simp [W]) with h|h
  · obtain ⟨k⟩ := h
    exact Or.inl ⟨j.symm.trans k⟩
  · obtain ⟨k⟩ := h
    exact Or.inr ⟨j.symm.trans k⟩

end QuadraticForm.BinarySixCoordinates
