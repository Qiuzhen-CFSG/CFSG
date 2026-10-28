module
public import Theory.GroupTheory.CubicCommutatorResidualImage
public import Theory.SpecificGroups.OrthogonalFourBinary.OddResidual
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.Omega
public import Theory.GroupTheory.ElementaryQuotientImage
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupAction.NormalPChiefSeries.FixedCodimension

public section
open Subgroup NoncentralChiefRefinement
open scoped IsMulCommutative commutatorElement
namespace OrthogonalFourBinary
open TerminalLines SylowGeometry

private def diagonalRotation : omega :=
  ⟨codeMap leftRotation * codeMap rightRotation,
    omega.mul_mem generators_mem_omega.1 generators_mem_omega.2.1⟩
private theorem diagonalRotation_apply (v : Space) :
    diagonalRotation.val.val v = rotation (Multiplicative.ofAdd (1,1)) v := by
  change candidate leftRotation (candidate rightRotation v) = _
  simp only [candidate_eval]
  exact (show ∀ v : Space, eval leftRotation (eval rightRotation v) =
    rotation (Multiplicative.ofAdd (1,1)) v from by decide +kernel) v
private theorem diagonalRotation_cube : diagonalRotation ^ 3 = 1 := by
  have he : diagonalRotation.val = rotationHom (Multiplicative.ofAdd (1,1)) :=
    Subtype.ext (LinearEquiv.ext diagonalRotation_apply)
  apply Subtype.ext
  change diagonalRotation.val ^ 3 = 1
  rw [he]
  exact rotation_cube _
private theorem diagonalRotation_fixed (v : Space) (hv : diagonalRotation.val.val v = v) :
    v = 0 := by
  rw [diagonalRotation_apply] at hv
  exact (show ∀ v : Space, rotation (Multiplicative.ofAdd (1,1)) v = v → v = 0 from
    by decide +kernel) v hv
private theorem diagonalRotation_difference (v : Space) :
    ∃ u : Space, diagonalRotation.val.val u - u = v := by
  simp only [diagonalRotation_apply]
  exact (show ∀ v : Space, ∃ u : Space, rotation (Multiplicative.ofAdd (1,1)) u - u = v from
    by decide +kernel) v

theorem omega_twoResidual_elementary : IsElementaryAbelian 3 (pResidual 2 omega) := by
  let : IsElementaryAbelian 3 (pResidual 2 IsometryGroup) := by
    rw [residual_eq_rotations]
    refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    rintro ⟨g,⟨i,rfl⟩⟩
    exact Subtype.ext (rotation_cube i)
  let f : pResidual 2 omega →* pResidual 2 IsometryGroup :=
    (omega.subtype.comp (pResidual 2 omega).subtype).codRestrict _
      (fun x => map_pResidual_le 2 omega.subtype (mem_map_of_mem omega.subtype x.property))
  exact IsElementaryAbelian.of_injective f (fun _ _ h =>
    Subtype.ext (Subtype.ext (congrArg (fun x : pResidual 2 IsometryGroup => (x : IsometryGroup)) h)))

variable {N : Type*} [Group N] [Finite N]

theorem commutatorResidual_geometry
    (W : Subgroup N) [W.Normal] [IsElementaryAbelian 2 W]
    (q : N →* omega) (hq : Function.Surjective q)
    (e : omega ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (x : Additive W ≃ₗ[ZMod 2] Space)
    (hx : ∀ n w, x (normalRepresentation W n w) = (q n).val.val (x w))
    (P : Subgroup N) (S : Sylow 2 omega) (hP : P.map q = S) :
    let X := cubicCommutatorResidual P
    ⁅W,X⁆ = W ∧ W ⊓ centralizer (X : Set N) = ⊥ ∧
      IsElementaryAbelian 3 (X.map (QuotientGroup.mk' (centralizer (W : Set N)))) ∧
      Nat.card (X.map (QuotientGroup.mk' (centralizer (W : Set N)))) = 9 := by
  let X := cubicCommutatorResidual P
  have him : X.map q = pResidual 2 omega :=
    cubicCommutatorResidual_map_of_symmetricThree_pair q hq e P S hP
  have hr : diagonalRotation ∈ pResidual 2 omega :=
    mem_pResidual_of_orderOf_coprime ((by decide : Nat.Coprime 2 3).of_dvd_right
      (orderOf_dvd_of_pow_eq_one diagonalRotation_cube))
  obtain ⟨r,hrX,hrq⟩ := (show diagonalRotation ∈ X.map q from him ▸ hr)
  have hker : q.ker = centralizer (W : Set N) := by
    ext n
    constructor
    · intro hn w hw
      have he := hx n (Additive.ofMul ⟨w,hw⟩)
      rw [MonoidHom.mem_ker.mp hn] at he
      have hfix := x.injective he
      have he' := congrArg (fun v : Additive W => (v.toMul : N)) hfix
      change n*w*n⁻¹=w at he'
      exact (mul_inv_eq_iff_eq_mul.mp he').symm
    · intro hn
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      change (q n).val.val v = v
      obtain ⟨w,rfl⟩ := x.surjective v
      rw [←hx]
      apply congrArg x
      apply Additive.toMul.injective
      apply Subtype.ext
      change n*(w.toMul:N)*n⁻¹=(w.toMul:N)
      rw [←hn w.toMul w.toMul.property,mul_inv_cancel_right]
  have hfixed : W ⊓ centralizer (X : Set N) = ⊥ := by
    apply bot_unique
    intro w hw
    have he := hx r (Additive.ofMul ⟨w,hw.1⟩)
    have hfix : normalRepresentation W r (Additive.ofMul ⟨w,hw.1⟩) =
        Additive.ofMul ⟨w,hw.1⟩ := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change r*w*r⁻¹=w
      rw [hw.2 r hrX,mul_inv_cancel_right]
    rw [hfix,hrq] at he
    have hz := x.injective ((diagonalRotation_fixed _ he.symm).trans (map_zero x).symm)
    exact congrArg (fun v : Additive W => (v.toMul : N)) hz
  refine ⟨?_,hfixed,?_,?_⟩
  · apply le_antisymm (commutator_le_left _ _)
    intro w hw
    obtain ⟨u,hu⟩ := diagonalRotation_difference (x (Additive.ofMul ⟨w,hw⟩))
    let y := x.symm u
    have he : normalRepresentation W r y - y = Additive.ofMul ⟨w,hw⟩ := by
      apply x.injective
      rw [map_sub,hx,hrq,LinearEquiv.apply_symm_apply]
      exact hu
    have he' := congrArg (fun v : Additive W => (v.toMul : N)) he
    rw [toMul_sub,Subgroup.coe_div,div_eq_mul_inv] at he'
    change r * (y.toMul:N) * r⁻¹ * (y.toMul:N)⁻¹ = w at he'
    rw [←he',commutator_comm]
    exact commutator_mem_commutator hrX y.toMul.property
  · apply elementary_quotient_image_of_exact_kernel X _ q hq hker
    rw [him]
    exact omega_twoResidual_elementary
  · have hc : Nat.card (X.map q) = 9 := by
      rw [him,←card_map_of_injective (f := e.toMonoidHom) e.injective,
        map_pResidual_of_surjective 2 e.toMonoidHom e.surjective]
      exact SymmetricThreeProductResidual.residual_card
    let a : (N ⧸ centralizer (W : Set N)) ≃* omega :=
      QuotientGroup.liftEquiv _ hq hker.symm
    have he : (X.map (QuotientGroup.mk' (centralizer (W : Set N)))).map a.toMonoidHom =
        X.map q := by rw [map_map]; rfl
    rw [←card_map_of_injective (f := a.toMonoidHom) a.injective,he]
    exact hc
end OrthogonalFourBinary
