/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
The binary plane-splitting formulas are adapted from the ATLAS-derived
ClassicalOrthogonal.SplitOdd.ReflectionGeneration.Complement development,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module
public import Theory.SpecificGroups.ClassicalOrthogonal.BinarySixResidual

/-!
# Cubic rank in higher binary orthogonal residuals

A nonsingular binary quadratic space of dimension at least eight contains
an actual minus-six orthogonal summand. Split off two hyperbolic planes;
the remaining space has dimension at least four, where a hyperbolic pair
and a nonsingular complement vector produce an anisotropic plane.

Extension by the identity embeds the full summand isometry group. Functoriality
of the solvable residual and the checked minus-six cubic subgroup give rank
at least three in the literal embedded residual of the original space.
All identifications are quadratic isometries, including the final universe
transport. The three plane steps have separate proof boundaries to avoid
expensive elaboration of nested complement types.

Source: the higher orthogonal branch of Aschbacher--Smith G.10.15, printed
p.363; the quadratic splitting and minus-six model results cited in the
imported modules.
-/

public noncomputable section
local instance {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Finite (V ≃ₗ[ZMod 2] V) := Finite.of_injective
  (fun a : V ≃ₗ[ZMod 2] V => (a : V → V)) DFunLike.coe_injective
open Module ClassicalOrthogonal.Quadratic
open ClassicalOrthogonal.Minus
namespace QuadraticForm.BinaryHigherCoordinates
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

private theorem exists_value_one {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) (hd : 0<finrank F V) :
    ∃ v : V,Q v=1 := by
  by_contra! hn
  have hz (v : V) : Q v=0 :=
    (show ∀ a : F,a=0 ∨ a=1 from by decide) (Q v) |>.resolve_right (hn v)
  have hall (x : V) : x=0 := hQ.1 x (fun y => by
    change Q (x+y)-Q x-Q y=0
    rw [hz,hz,hz,sub_self,sub_zero])
  let : Subsingleton V := ⟨fun x y => (hall x).trans (hall y).symm⟩
  have hh : finrank F V=0 := Module.finrank_zero_of_subsingleton
  omega

/-- In dimension at least four, a hyperbolic plane and a nonsingular
complement vector explicitly produce an anisotropic plane. -/
theorem exists_anisotropic_pair {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) (hd : 4≤finrank F V) :
    ∃ a b : V,Q a=1 ∧ Q b=1 ∧ Q.polarBilin a b=1 := by
  obtain ⟨e,f,he,hf,hef⟩ := hyperbolic_pair Q hQ (by omega)
  have hc := complement_nd Q hQ e f he hf hef
  have hdim := finrank_complement Q e f he hf hef
  obtain ⟨z,hz⟩ := exists_value_one (complementForm Q e f) hc (by omega)
  have hze : Q.polarBilin z.val e=0 := z.property.1
  have hzf : Q.polarBilin z.val f=0 := z.property.2
  have hqz : Q z.val=1 := hz
  refine ⟨e+f,e+z.val,?_,?_,?_⟩
  · rw [QuadraticMap.map_add Q]
    change Q e+Q f+Q.polarBilin e f=1
    rw [he,hf,hef,zero_add,zero_add]
  · rw [QuadraticMap.map_add Q]
    change Q e+Q z.val+Q.polarBilin e z.val=1
    rw [he,hqz,polar_swap Q e z.val,hze,zero_add,add_zero]
  · simp only [map_add,LinearMap.add_apply,polar_self,he,mul_zero,zero_add]
    rw [polar_swap Q e z.val,hze,polar_swap Q f e,hef,
      polar_swap Q f z.val,hzf]
    simp



private def anisotropicSplit {V : Type} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (e f : V) (hef : Q.polarBilin e f=1) :
    V ≃ₗ[F] Plane × complement Q e f where
  toFun x := ((Q.polarBilin x f,Q.polarBilin x e),
    ⟨x-planeProjection Q e f x,by
      have hfe := (polar_swap Q f e).trans hef
      simp only [mem_complement,planeProjection_apply,map_sub,map_add,map_smul,
        LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,
        polar_self,show (2 : F)=0 from by decide,zero_mul,hef,hfe]
      constructor <;> ring⟩)
  invFun z := z.1.1 • e+z.1.2 • f+z.2.val
  left_inv x := by simp only [planeProjection_apply]; module
  right_inv z := by
    rcases z with ⟨⟨r,s⟩,⟨w,hw⟩⟩
    have hw := (mem_complement Q e f w).mp hw
    have hfe := (polar_swap Q f e).trans hef
    apply Prod.ext
    · apply Prod.ext <;>
        simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
          smul_eq_mul,polar_self,show (2 : F)=0 from by decide,zero_mul,
          hef,hfe,hw.1,hw.2,mul_zero,mul_one,zero_add,add_zero]
    · apply Subtype.ext
      simp only [planeProjection_apply,map_add,map_smul,polar_self,
        show (2 : F)=0 from by decide,zero_mul,hef,hfe,hw.1,hw.2]
      module
  map_add' x y := by
    apply Prod.ext
    · simp only [map_add,LinearMap.add_apply,Prod.mk_add_mk]
    · apply Subtype.ext
      change x+y-planeProjection Q e f (x+y)=
        (x-planeProjection Q e f x)+(y-planeProjection Q e f y)
      rw [map_add]
      module
  map_smul' a x := by
    apply Prod.ext
    · simp only [map_smul,LinearMap.smul_apply,Prod.smul_mk,RingHom.id_apply]
    · apply Subtype.ext
      change a • x-planeProjection Q e f (a • x)=a • (x-planeProjection Q e f x)
      rw [map_smul,smul_sub]

private def anisotropicIsometry {V : Type} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (e f : V) (he : Q e=1) (hf : Q f=1)
    (hef : Q.polarBilin e f=1) : Q.IsometryEquiv (A.prod (complementForm Q e f)) where
  toLinearEquiv := anisotropicSplit Q e f hef
  map_app' x := by
    have hform (z : Plane × complement Q e f) :
        Q ((anisotropicSplit Q e f hef).symm z) = A z.1+Q z.2.val := by
      rcases z with ⟨⟨r,s⟩,⟨w,hw⟩⟩
      have hw := (mem_complement Q e f w).mp hw
      have hew := (polar_swap Q e w).trans hw.1
      have hfw := (polar_swap Q f w).trans hw.2
      change Q (r • e+s • f+w)=plane F 1 (r,s)+Q w
      rw [QuadraticMap.map_add Q,QuadraticMap.map_add Q,plane_apply]
      change Q (r • e)+Q (s • f)+Q.polarBilin (r • e) (s • f)+Q w+
        Q.polarBilin (r • e+s • f) w=_
      simp only [Q.map_smul,map_smul,map_add,LinearMap.add_apply,LinearMap.smul_apply,
        smul_eq_mul,he,hf,hef,hew,hfw,CharTwo.sub_eq_add]
      ring
    exact (hform ((anisotropicSplit Q e f hef) x)).symm.trans
      (congrArg Q ((anisotropicSplit Q e f hef).symm_apply_apply x))

private def reassociate {V W X : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup X]
    [Module F V] [Module F W] [Module F X]
    (q : QuadraticForm F V) (r : QuadraticForm F W) (t : QuadraticForm F X) :
    (q.prod (r.prod t)).IsometryEquiv ((q.prod r).prod t) where
  toLinearEquiv := (LinearEquiv.prodAssoc F V W X).symm
  map_app' _ := (add_assoc _ _ _)
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



end QuadraticForm.BinaryHigherCoordinates
open Subgroup Module
namespace BinaryOrthogonalRank
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]
  [Module (ZMod 2) V] [Module (ZMod 2) W]
variable (q : QuadraticForm (ZMod 2) V) (r : QuadraticForm (ZMod 2) W)

private def prodLeft : q.isometrySubgroup →* (q.prod r).isometrySubgroup where
  toFun a := ⟨a.val.prodCongr (LinearEquiv.refl (ZMod 2) W), by
    apply (QuadraticMap.mem_isometrySubgroup _ _).mpr
    intro x
    change q (a.val x.1)+r x.2=q x.1+r x.2
    rw [(QuadraticMap.mem_isometrySubgroup _ _).mp a.property]⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rfl
  map_mul' a b := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rfl

private theorem prodLeft_injective : Function.Injective (prodLeft q r) := by
  intro a b h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact congrArg (fun g : (q.prod r).isometrySubgroup => (g.val (x,0)).1) h

/-- An actual orthogonal direct summand injects its solvable residual into
the full space's residual. -/
theorem residual_primeRank_le_prod [Finite V] [Finite W] (p : ℕ) :
    primeRank p (solvableResidual q.isometrySubgroup) ≤
      primeRank p (solvableResidual (q.prod r).isometrySubgroup) := by
  let : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun a : V ≃ₗ[ZMod 2] V => (a : V → V)) DFunLike.coe_injective
  let : Finite ((V × W) ≃ₗ[ZMod 2] (V × W)) :=
    Finite.of_injective (fun a : (V × W) ≃ₗ[ZMod 2] (V × W) => (a : V × W → V × W)) DFunLike.coe_injective
  let f := (prodLeft q r).comp (solvableResidual q.isometrySubgroup).subtype
  have hf : ∀ a,f a∈solvableResidual (q.prod r).isometrySubgroup := by
    intro a
    exact (map_solvableResidual_le (prodLeft q r)) ⟨a.val,a.property,rfl⟩
  let g := f.codRestrict _ hf
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    exact prodLeft_injective q r (congrArg Subtype.val h)
  exact primeRank_le_of_injective p g hg
end BinaryOrthogonalRank

namespace QuadraticForm.BinaryHigherCoordinates
open Subgroup
private theorem residual_rank_congr {G K : Type*} [Group G] [Group K]
    [Finite G] [Finite K] (e : G ≃* K) (p : ℕ) :
    primeRank p (solvableResidual G)=primeRank p (solvableResidual K) := by
  let f := ((solvableResidual G).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_solvableResidual_eq e.toMonoidHom e.surjective))
  exact primeRank_congr p f

private theorem minus_six_rank : 3≤primeRank 3 (solvableResidual (quadraticForm F 3).isometrySubgroup) := by
  have heq : (quadraticForm F 3).isometrySubgroup=
      Theory.AlgebraicGroup.quadraticIsometrySubgroup (quadraticForm F 3) := by
    ext g
    exact (QuadraticMap.mem_isometrySubgroup _ g).trans
      (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ g).symm
  have h := (QuadraticForm.BinarySixResidual.minus_six_residual
    (quadraticForm F 3).isometrySubgroup (MulEquiv.subgroupCongr heq)).2
  rw [← primeRank_congr 3 ((solvableResidual (quadraticForm F 3).isometrySubgroup).equivMapOfInjective
     (quadraticForm F 3).isometrySubgroup.subtype
      (quadraticForm F 3).isometrySubgroup.subtype_injective)] at h
  exact h

private theorem two_hyperbolic_rank {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) (hd : 4≤finrank F V) :
    3≤primeRank 3 (solvableResidual (H.prod (H.prod Q)).isometrySubgroup) := by
  let : Finite V := Module.finite_of_finite F
  obtain ⟨z,w,hz,hw,hzw⟩ := exists_anisotropic_pair Q hQ hd
  let E := complementForm Q z w
  let e2 := anisotropicIsometry Q z w hz hw hzw
  let j := (QuadraticMap.IsometryEquiv.refl H).prod
    ((QuadraticMap.IsometryEquiv.refl H).prod e2)
  let k := j.trans (((QuadraticMap.IsometryEquiv.refl H).prod (reassociate H A E)).trans
    ((reassociate H (H.prod A) E).trans
      (minusIsometry.prod (QuadraticMap.IsometryEquiv.refl E))))
  rw [residual_rank_congr k.isometrySubgroupCongr 3]
  exact minus_six_rank.trans (BinaryOrthogonalRank.residual_primeRank_le_prod _ E 3)

private theorem one_hyperbolic_rank {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) (hd : 6≤finrank F V) :
    3≤primeRank 3 (solvableResidual (H.prod Q).isometrySubgroup) := by
  let : Finite V := Module.finite_of_finite F
  obtain ⟨e,f,he,hf,hef⟩ := hyperbolic_pair Q hQ (by omega)
  let C := complementForm Q e f
  have hC := complement_nd Q hQ e f he hf hef
  have hdC : 4≤finrank F (complement Q e f) := by
    have := finrank_complement Q e f he hf hef
    omega
  let k := (QuadraticMap.IsometryEquiv.refl H).prod (splitIsometry Q e f he hf hef)
  rw [residual_rank_congr k.isometrySubgroupCongr 3]
  exact two_hyperbolic_rank C hC hdC

/-- Two hyperbolic planes and an anisotropic plane embed the minus-six
residual into every nonsingular binary space of dimension at least eight. -/
theorem residual_rank_ge_three_coordinate {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) (hd : 8≤finrank F V) :
    3≤primeRank 3 (solvableResidual Q.isometrySubgroup) := by
  let : Finite V := Module.finite_of_finite F
  obtain ⟨e,f,he,hf,hef⟩ := hyperbolic_pair Q hQ (by omega)
  let C := complementForm Q e f
  have hC := complement_nd Q hQ e f he hf hef
  have hdC : 6≤finrank F (complement Q e f) := by
    have := finrank_complement Q e f he hf hef
    omega
  rw [residual_rank_congr (splitIsometry Q e f he hf hef).isometrySubgroupCongr 3]
  exact one_hyperbolic_rank C hC hdC

/-- The cubic rank obstruction is intrinsic, with no restriction on the
universe or coordinates of the original quadratic space. -/
theorem residual_rank_ge_three {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) (hd : 8≤finrank F V) :
    3≤primeRank 3 ((solvableResidual Q.isometrySubgroup).map Q.isometrySubgroup.subtype) := by
  let W := Fin (finrank F V) → F
  let e : W ≃ₗ[F] V := (finBasis F V).equivFun.symm
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
  let : Finite V := Module.finite_of_finite F
  let : Finite (V ≃ₗ[F] V) := Finite.of_injective
    (fun a : V ≃ₗ[F] V => (a : V → V)) DFunLike.coe_injective
  have hr := residual_rank_ge_three_coordinate P hn (by simpa [W] using hd)
  rw [residual_rank_congr j.isometrySubgroupCongr 3] at hr
  rw [← primeRank_congr 3 ((solvableResidual Q.isometrySubgroup).equivMapOfInjective
     Q.isometrySubgroup.subtype Q.isometrySubgroup.subtype_injective)]
  exact hr
end QuadraticForm.BinaryHigherCoordinates
